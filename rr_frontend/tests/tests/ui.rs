use std::env;
use std::path::PathBuf;

use ui_test::color_eyre;
use ui_test::spanned::Spanned;

fn rustc_path() -> PathBuf {
    let target_dir = env::var_os("CARGO_TARGET_DIR").map_or_else(
        || PathBuf::from(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("target"),
        PathBuf::from,
    );

    target_dir
        .join(if cfg!(debug_assertions) { "debug" } else { "release" })
        .join("refinedrust-rustc")
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let mut config = ui_test::Config::rustc("fail");
    config.comment_defaults.base().env_vars = vec![("RR_VERIFY_DEPS".to_owned(), "true".to_owned())];
    config.program.program = rustc_path();
    config.custom_comments.insert("stderr-only", |parser, _args, span| {
        parser.require_annotations = Spanned::new(false, span).into();
    });

    let abort_check = config.abort_check.clone();
    ctrlc::set_handler(move || abort_check.abort())?;

    ui_test::run_tests(config)
}
