use which::which;

pub mod command;

#[must_use]
pub fn find(cmd: &str) -> Option<String> {
    let Ok(cmd) = which(cmd) else {
        return None;
    };

    Some(cmd.to_str()?.to_owned())
}
