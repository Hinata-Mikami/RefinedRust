// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

#![feature(rustc_private)]

use std::path::PathBuf;
use std::process::Command;
use std::{env, process};

use lib::command;

static USAGE: &str = "RefinedRust verification framework

Usage: cargo refinedrust [Cargo options] -- [RefinedRust options]

RefinedRust Options:
  -h, --help               Print help
      --show-config        Display the detected configuration
  -V, --version            Print version info";

fn dump_version_info() {
    println!("RefinedRust {}", env!("RR_VERSION"));
    println!("{} ({})", env!("RR_RUSTC_VERSION"), env!("RR_RUSTC"));
    println!("{} ({})", env!("RR_CARGO_VERSION"), env!("RR_CARGO"));

    let Some(dune) = lib::find("dune") else { return println!("dune not found") };
    println!("dune {} ({})", command::get_cmd_output(&dune, &["--version"]).unwrap(), dune);

    let Some(rocq) = lib::find("rocq") else { return println!("rocq not found") };
    let rocq_version = command::get_cmd_output(&rocq, &["--print-version"]).unwrap();
    let rocq_version = rocq_version.split(' ').next().unwrap();
    println!("rocq {} ({})", rocq_version, rocq);
}

/// Returns the arguments for `RefinedRust` and `cargo`.
fn get_args() -> (Vec<String>, Vec<String>) {
    let args: Vec<String> = env::args().skip(1).skip_while(|arg| arg == "refinedrust").collect();
    let args_index = args.iter().position(|arg| arg == "--").unwrap_or(args.len());

    let (rr_args, cargo_args): (&[String], &[String]) = args.split_at(args_index);
    let rr_args: Vec<String> = rr_args.iter().map(ToOwned::to_owned).collect();
    let cargo_args: Vec<String> = cargo_args.iter().map(ToOwned::to_owned).skip(1).collect();

    (rr_args, cargo_args)
}

fn main() {
    let (rr_args, cargo_args) = get_args();

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

    process(cargo_args).unwrap_or_else(|c| process::exit(c));
}

fn process(cargo_args: Vec<String>) -> Result<(), i32> {
    // can we make this more robust?
    let mut rr_rustc_path = env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("refinedrust-rustc");
    if cfg!(windows) {
        rr_rustc_path.set_extension("exe");
    }

    // TODO: If we're using workspaces, we should figure out the right dir for the workspace
    let cargo_target_path = env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_owned());
    let cargo_target = PathBuf::from(cargo_target_path.clone());

    let output_dir = rrconfig::output_dir()
        .unwrap_or_else(|| [cargo_target_path, "verify".to_owned()].into_iter().collect());

    let exit_status = Command::new(env!("RR_CARGO"))
        .arg("check")
        .args(cargo_args)
        .env("RUSTC", rr_rustc_path)
        .env("CARGO_TARGET_DIR", &cargo_target)
        .env("RR_OUTPUT_DIR", &output_dir)
        .status()
        .expect("could not run cargo");

    if exit_status.success() { Ok(()) } else { Err(exit_status.code().unwrap_or(-1)) }
}
