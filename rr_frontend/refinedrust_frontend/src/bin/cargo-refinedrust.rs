// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

#![feature(rustc_private)]

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Command;
use std::{env, process};

use lib::command;

static USAGE: &str = "RefinedRust verification framework

Usage: cargo refinedrust [<RefinedRust options>] -- [<cargo options>]

RefinedRust Options:
      --no-assumption      Require specifications to not be assumed
      --show-config        Display the detected configuration
  -h, --help               Print help
  -V, --version            Print version info";

fn main() {
    let rr_rustc_path = get_rustc_path();
    let cargo_target = get_cargo_target_path();

    let mut rr_env: HashMap<&str, &str> = HashMap::new();
    let (rr_args, cargo_args) = get_args();

    for arg in &rr_args {
        match arg.as_str() {
            "-h" | "--help" => return println!("{}", USAGE),
            "-V" | "--version" => return dump_version_info(),

            "--no-assumption" => {
                rr_env.insert("RR_NO_ASSUMPTION", "true");
            },

            "--show-config" => {
                run(Command::new(&rr_rustc_path).arg("--show-config"), rr_env);
            },

            _ => {
                eprintln!("Unexpected argument: {}", arg);
                eprintln!("Use `cargo refinedrust --help` for usage information.");
                process::exit(1);
            },
        }
    }

    run(
        Command::new(env!("RR_CARGO"))
            .arg("check")
            .args(cargo_args)
            .env("RUSTC", rr_rustc_path)
            .env("CARGO_TARGET_DIR", &cargo_target),
        rr_env,
    );
}

fn run(cmd: &mut Command, rr_env: HashMap<&str, &str>) -> ! {
    let output_dir = rrconfig::output_dir()
        .unwrap_or_else(|| [get_cargo_target_path(), "verify".to_owned()].into_iter().collect());

    let cmd = cmd.env("RR_OUTPUT_DIR", &output_dir).envs(rr_env);

    let exit_status = cmd
        .status()
        .unwrap_or_else(|_| panic!("could not run {}", cmd.get_program().to_str().unwrap()));

    if exit_status.success() {
        process::exit(0);
    } else {
        process::exit(exit_status.code().unwrap_or(-1))
    }
}

fn dump_version_info() {
    println!("RefinedRust {}", env!("RR_VERSION"));

    println!();
    println!("RefinedRust library paths:");
    for lib in rrconfig::lib_load_paths() {
        println!(" - {}", lib.display());
    }

    println!();
    println!("Rust toolchain:");
    println!(" - {} ({})", env!("RR_RUSTC_VERSION"), env!("RR_RUSTC"));
    println!(" - {} ({})", env!("RR_CARGO_VERSION"), env!("RR_CARGO"));

    println!();
    println!("Rocq toolchain:");

    let Some(dune) = lib::find("dune") else { return println!(" - dune not found") };
    let Some(dune_version) = command::get_cmd_output(&dune, &["--version"]) else {
        return println!(" - unexpected dune output");
    };

    let Some(rocq) = lib::find("rocq") else { return println!(" - rocq not found") };
    let Some(rocq_version) = command::get_cmd_output(&rocq, &["--print-version"])
        .and_then(|output| output.split(' ').next().map(ToOwned::to_owned))
    else {
        return println!(" - unexpected rocq output");
    };

    println!(" - dune {} ({})", dune_version, dune);
    println!(" - rocq {} ({})", rocq_version, rocq);
}

fn get_rustc_path() -> PathBuf {
    let mut rr_rustc_path = env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("refinedrust-rustc");

    if cfg!(windows) {
        rr_rustc_path.set_extension("exe");
    }

    rr_rustc_path
}

fn get_cargo_target_path() -> String {
    // TODO: If we're using workspaces, we should figure out the right dir for the workspace
    env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_owned())
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
