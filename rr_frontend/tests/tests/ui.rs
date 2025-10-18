use std::env;
use std::path::PathBuf;

use ui_test::color_eyre;

fn rustc_path() -> PathBuf {
    let mut path = env::current_exe().unwrap();
    path.pop();
    path.pop();

    path.join("refinedrust-rustc")
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let mut config = ui_test::Config::rustc("fail");
    config.comment_defaults.base().env_vars = vec![("RR_VERIFY_DEPS".to_owned(), "true".to_owned())];
    config.program.program = rustc_path();

    let abort_check = config.abort_check.clone();
    ctrlc::set_handler(move || abort_check.abort())?;

    ui_test::run_tests(config)
}
