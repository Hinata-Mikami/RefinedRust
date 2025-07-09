// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::env;

use which::which;

include!("src/command.rs");

fn add_variable(name: &str, value: &str) {
    println!("cargo::rustc-env={}={}", name, value);
}

fn get_rr_version() -> String {
    let version = env!("CARGO_PKG_VERSION").to_owned();

    let Some(git_version) = get_cmd_output("git", &["rev-parse", "--short", "HEAD"]) else {
        return version;
    };

    format!("{} ({})", version, git_version)
}

fn main() {
    let cargo = which(env::var("CARGO").unwrap()).unwrap();
    let rustc = which(env::var("RUSTC").unwrap()).unwrap();

    add_variable("RR_VERSION", &get_rr_version());

    add_variable("RR_RUSTC", rustc.to_str().unwrap());
    add_variable("RR_RUSTC_VERSION", &get_cmd_output("rustc", &["--version"]).unwrap());

    add_variable("RR_CARGO", cargo.to_str().unwrap());
    add_variable("RR_CARGO_VERSION", &get_cmd_output("cargo", &["--version"]).unwrap());
}
