// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

pub(crate) mod flat;
pub(crate) mod registry;

use std::collections::HashMap;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::{fs, io};

/// Find `RefinedRust` modules in the given loadpath.
fn scan_loadpath(path: &Path, storage: &mut HashMap<String, PathBuf>) -> io::Result<()> {
    if path.is_dir() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                scan_loadpath(path.as_path(), storage)?;
            } else if path.is_file()
                && let Some(ext) = path.extension()
                && Some("rrlib") == ext.to_str()
            {
                // try to open this rrlib file
                let f = File::open(path.clone())?;
                if let Some(name) = registry::is_valid_refinedrust_module(f) {
                    storage.insert(name, path);
                }
            }
        }
    }

    Ok(())
}

/// Find `RefinedRust` modules in the given loadpaths.
pub(crate) fn scan_loadpaths(paths: &[PathBuf]) -> io::Result<HashMap<String, PathBuf>> {
    let mut found_lib_files: HashMap<String, PathBuf> = HashMap::new();

    for path in paths {
        scan_loadpath(path, &mut found_lib_files)?;
    }

    Ok(found_lib_files)
}
