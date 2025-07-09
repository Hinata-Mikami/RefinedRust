// This file is also included in `build.rs`

use std::process::Command;

#[must_use]
pub fn get_cmd_output(command: &str, args: &[&str]) -> Option<String> {
    let Ok(output) = Command::new(command).args(args).output() else {
        return None;
    };

    if !output.status.success() {
        return None;
    }

    Some(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}
