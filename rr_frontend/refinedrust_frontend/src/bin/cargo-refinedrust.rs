// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

#![feature(rustc_private)]

use std::path::PathBuf;
use std::process::Command;
use std::{env, process};

static USAGE: &str = "RefinedRust verification framework

Usage: cargo refinedrust [Cargo options] -- [RefinedRust options]

RefinedRust Options:
  -h, --help               Print help
      --show-config        Display the detected configuration
  -V, --version            Print version info";

fn dump_version_info() {
    println!("RefinedRust version: {}", env!("CARGO_PKG_VERSION"));
}

fn main() {
    let args: Vec<String> = env::args().skip(1).skip_while(|arg| arg == "refinedrust").collect();
    let args_index = args.iter().position(|arg| arg == "--").unwrap_or(args.len());

    let (rr_args, cargo_args): (&[String], &[String]) = args.split_at(args_index);
    let rr_args: Vec<String> = rr_args.iter().map(ToOwned::to_owned).collect();
    let cargo_args: Vec<String> = cargo_args.iter().map(ToOwned::to_owned).skip(1).collect();

    if rr_args.iter().any(|arg| arg == "-h" || arg == "--help") {
        return println!("{}", USAGE);
    }

    if rr_args.iter().any(|arg| arg == "-V" || arg == "--version") {
        return dump_version_info();
    }

    if rr_args.iter().any(|arg| arg == "--show-config") {
        println!("Current detected configuration:");
        return print!("{}", rrconfig::dump());
    }

    if !rr_args.is_empty() {
        eprintln!("Unexpected arguments: {}", rr_args.join(" "));
        eprintln!("Use `cargo refinedrust --help` for usage information.");
        process::exit(1);
    }

    if let Err(code) = process(cargo_args) {
        process::exit(code);
    }
}

fn process(cargo_args: Vec<String>) -> Result<(), i32> {
    // can we make this more robust?
    let mut rr_rustc_path = env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("refinedrust-rustc");
    if cfg!(windows) {
        rr_rustc_path.set_extension("exe");
    }

    let cargo_path = rrconfig::cargo_path();
    let command = rrconfig::cargo_command();

    // TODO: If we're using workspaces, we should figure out the right dir for the workspace
    let cargo_target_path = env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_owned());
    let cargo_target = PathBuf::from(cargo_target_path.clone());

    let output_dir = rrconfig::output_dir()
        .unwrap_or_else(|| [cargo_target_path, "verify".to_owned()].into_iter().collect());

    let exit_status = Command::new(cargo_path)
        .arg(&command)
        .args(cargo_args)
        .env("RUSTC", rr_rustc_path)
        .env("CARGO_TARGET_DIR", &cargo_target)
        .env("RR_CARGO", "")
        .env("RR_OUTPUT_DIR", &output_dir)
        .status()
        .expect("could not run cargo");

    if exit_status.success() { Ok(()) } else { Err(exit_status.code().unwrap_or(-1)) }
}
