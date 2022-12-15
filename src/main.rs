// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use anyhow::Result;
use fxhash::FxHashMap;
use regex::Regex;
use std::collections::hash_map::Entry;
use std::env;
use std::io::{self, BufRead, Write};
use std::path::Path;
use std::str;
use wholesym::FramesLookupResult;
use wholesym::SymbolManager;
use wholesym::SymbolManagerConfig;
use wholesym::SymbolMap;

#[cfg(test)]
mod tests;

enum JsonMode {
    No,
    Yes,
}

/// Info provided via the `-b` flag.
struct BreakpadInfo {
    syms_dir: String,
}

/// The top level structure that does the work.
struct Fixer {
    re: Regex,
    symbol_manager: SymbolManager,
    file_infos: FxHashMap<String, Option<SymbolMap>>,
    json_mode: JsonMode,
    lb: char,
    rb: char,
}

impl Fixer {
    fn new(json_mode: JsonMode, bp_info: Option<BreakpadInfo>) -> Fixer {
        // We use parentheses with native debug info, and square brackets with
        // Breakpad symbols.
        let (lb, rb) = if bp_info.is_none() {
            ('(', ')')
        } else {
            ('[', ']')
        };
        let config = SymbolManagerConfig::default().verbose(true);
        let config = match bp_info {
            Some(bp_info) => config.breakpad_symbols_dir(bp_info.syms_dir),
            None => config,
        };
        Fixer {
            // Matches lines produced by MozFormatCodeAddress().
            re: Regex::new(r"^(.*#\d+: )(.+)\[(.+) \+0x([0-9A-Fa-f]+)\](.*)$").unwrap(),
            symbol_manager: SymbolManager::with_config(config),
            file_infos: FxHashMap::default(),
            json_mode,
            lb,
            rb,
        }
    }

    /// Add JSON escapes to a fragment of text.
    fn json_escape(string: &str) -> String {
        // Do the escaping.
        let escaped = serde_json::to_string(string).unwrap();

        // Strip the quotes.
        escaped[1..escaped.len() - 1].to_string()
    }

    /// Remove JSON escapes from a fragment of text.
    fn json_unescape(string: &str) -> String {
        // Add quotes.
        let quoted = format!("\"{}\"", string);

        // Do the unescaping, which also removes the quotes.
        let value = serde_json::from_str(&quoted).unwrap();
        if let serde_json::Value::String(unescaped) = value {
            unescaped
        } else {
            panic!()
        }
    }

    /// Read the data from `file_name` and construct a `FileInfo` that we can
    /// subsequently query. Return a description of the failing operation on
    /// error.
    fn build_file_info(symbol_manager: &SymbolManager, bin_file: &str) -> Result<SymbolMap> {
        let symbol_map = futures::executor::block_on(
            symbol_manager.load_symbol_map_for_binary_at_path(Path::new(bin_file), None),
        )?;
        Ok(symbol_map)
    }

    /// Strip any annoying Firefox Breakpad junk from this filename. E.g.
    /// `hg:hg.mozilla.org/integration/autoland:caps/BasePrincipal.cpp:04c31e994f29e72dd81a7340100d12f67e48a5b4`
    /// becomes `caps/BasePrincipal.cpp`.
    ///
    /// It's not perfect, e.g. it will fail if the filename contains a colon.
    /// But that should happen almost never, and if it does the junk won't be
    /// stripped, which is still a reasonable outcome.
    fn strip_firefox_breakpad_junk(file_name: &str) -> Option<&str> {
        // Split on the colons.
        let mut iter = file_name.split(':');

        // Is the first element "hg"?
        let s1 = iter.next()?;
        if s1 != "hg" {
            return None;
        }

        // Does the second element start with "hg.mozilla.org"?
        let s2 = iter.next()?;
        if !s2.starts_with("hg.mozilla.org") {
            return None;
        }

        // The third element is the one we want.
        let s3 = iter.next()?;

        // Is the fourth element a hex id of length 40?
        let s4 = iter.next()?;
        if s4.len() != 40 || !s4.chars().all(|c| c.is_ascii_hexdigit()) {
            return None;
        }

        // Is there no fifth element?
        if iter.next().is_some() {
            return None;
        }

        // It's a match. Return the interesting part.
        Some(s3)
    }

    /// Fix stack frames within `line` as necessary. Prints any errors to stderr.
    #[inline]
    fn fix(&mut self, line: String) -> String {
        // Apply the regexp.
        let captures = if let Some(captures) = self.re.captures(&line) {
            captures
        } else {
            return line;
        };

        let before = &captures[1];
        let in_func_name = &captures[2];
        let in_file_name = &captures[3];
        let address = u64::from_str_radix(&captures[4], 16).unwrap();
        let after = &captures[5];

        // In JSON mode, unescape the function name before using it for
        // lookups, error messages, etc.
        let raw_in_file_name = if let JsonMode::Yes = self.json_mode {
            Fixer::json_unescape(in_file_name)
        } else {
            in_file_name.to_string()
        };

        // If we haven't seen this file yet, parse and record its contents, for
        // this lookup and any future lookups.
        let symbol_map = match self.file_infos.entry(raw_in_file_name.clone()) {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => {
                match Self::build_file_info(&self.symbol_manager, &raw_in_file_name) {
                    Ok(file_info) => v.insert(Some(file_info)),
                    Err(err) => {
                        // Print an error message and then set up an empty
                        // `FileInfo` for this file, for two reasons.
                        // - If an invalid file is mentioned multiple times in the
                        //   input, an error message will be issued only on the
                        //   first occurrence.
                        // - The line will still receive some transformation, using
                        //   the "no symbols or debug info" case below.
                        eprintln!(
                            "fix-stacks: error: failed to {} `{}`",
                            err, raw_in_file_name
                        );
                        err.chain()
                            .skip(1)
                            .for_each(|cause| eprintln!("fix-stacks: {}", cause));

                        v.insert(None)
                    }
                }
            }
        };

        // In JSON mode, we need to escape any new strings we produce. However,
        // strings from the input (i.e. `in_func_name` and `in_file_name`),
        // will already be escaped, so if they are used in the output they
        // shouldn't be re-escaped.
        if let Some(address_info) = symbol_map
            .as_ref()
            .and_then(|symbol_map| symbol_map.lookup(address as u32))
        {
            let raw_out_func_name = address_info.symbol.name;
            let out_func_name = if let JsonMode::Yes = self.json_mode {
                Fixer::json_escape(&raw_out_func_name)
            } else {
                raw_out_func_name
            };

            let frames = match address_info.frames {
                FramesLookupResult::Available(frames) => Some(frames),
                FramesLookupResult::External(ext_lookup) => {
                    futures::executor::block_on(self.symbol_manager.lookup_external(&ext_lookup))
                }
                FramesLookupResult::Unavailable => None,
            };
            match frames.as_deref() {
                Some(&[.., ref last_frame]) if last_frame.file_path.is_some() => {
                    // We have the function name, filename, and line number from
                    // the debug info.
                    let raw_out_file_name = last_frame.file_path.as_ref().unwrap().mapped_path();
                    let out_file_name_str;
                    let mut out_file_name = if let JsonMode::Yes = self.json_mode {
                        out_file_name_str = Fixer::json_escape(&raw_out_file_name);
                        out_file_name_str.as_str()
                    } else {
                        &raw_out_file_name
                    };

                    // Maybe strip some junk from Breakpad file names.
                    if let Some(stripped) = Fixer::strip_firefox_breakpad_junk(out_file_name) {
                        out_file_name = stripped;
                    }

                    let line_str = match last_frame.line_number {
                        Some(line) => line.to_string(),
                        None => "?".to_string(),
                    };

                    format!(
                        "{}{} {}{}:{}{}{}",
                        before, out_func_name, self.lb, out_file_name, line_str, self.rb, after
                    )
                }
                _ => {
                    // We have the function name from the debug info, but no file
                    // name or line number. Use the file name and address from the
                    // original input.
                    format!(
                        "{}{} {}{} + 0x{:x}{}{}",
                        before, out_func_name, self.lb, in_file_name, address, self.rb, after
                    )
                }
            }
        } else {
            // We have nothing from the debug info. Use the function name, file
            // name, and address from the original input. The end result is the
            // same as the original line, but with slightly different
            // formatting.
            format!(
                "{}{} {}{} + 0x{:x}{}{}",
                before, in_func_name, self.lb, in_file_name, address, self.rb, after
            )
        }
    }
}

#[rustfmt::skip]
const USAGE_MSG: &str =
r##"usage: fix-stacks [options] < input > output

Post-process the stack frames produced by MozFormatCodeAddress().

options:
  -h, --help              Show this message and exit
  -j, --json              Treat input and output as JSON fragments
  -b, --breakpad DIR      Use breakpad symbols in directory DIR
"##;

fn main_inner() -> io::Result<()> {
    // Process command line arguments. The arguments are simple enough for now
    // that using an external crate doesn't seem worthwhile.
    let mut json_mode = JsonMode::No;
    let mut bp_info = None;

    let err = |msg| Err(io::Error::new(io::ErrorKind::Other, msg));

    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        if arg == "-h" || arg == "--help" {
            println!("{}", USAGE_MSG);
            return Ok(());
        } else if arg == "-j" || arg == "--json" {
            json_mode = JsonMode::Yes;
        } else if arg == "-b" || arg == "--breakpad" {
            match args.next() {
                Some(arg2) => {
                    bp_info = Some(BreakpadInfo {
                        syms_dir: arg2.to_string(),
                    });
                }
                _ => {
                    return err(format!("missing argument to option `{}`.", arg));
                }
            }
        } else {
            let msg = format!(
                "bad argument `{}`. Run `fix-stacks -h` for more information.",
                arg
            );
            return err(msg);
        }
    }

    let reader = io::BufReader::new(io::stdin());

    let mut fixer = Fixer::new(json_mode, bp_info);
    for line in reader.lines() {
        writeln!(io::stdout(), "{}", fixer.fix(line.unwrap()))?;
    }

    Ok(())
}

fn main() {
    // Ignore broken pipes, e.g. when piping output through `head -10`.
    if let Err(err) = main_inner() {
        if err.kind() != io::ErrorKind::BrokenPipe {
            eprintln!("fix-stacks: {}", err);
            std::process::exit(1);
        }
    }
}
