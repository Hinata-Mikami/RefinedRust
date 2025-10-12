#![feature(rustc_private)]

// Sources:
// https://github.com/rust-lang/miri/blob/master/benches/helpers/miri_helper.rs
// https://github.com/rust-lang/rust/blob/master/src/test/run-make-fulldeps/obtain-borrowck/driver.rs

use std::cell::RefCell;
use std::mem;
use std::env;
use std::process;

use analysis::abstract_interpretation::FixpointEngine as _;
use analysis::domains::DefinitelyInitializedAnalysis;
use rr_rustc_interface::borrowck::consumers::{self, BodyWithBorrowckFacts};
use rr_rustc_interface::data_structures::fx::FxHashMap;
use rr_rustc_interface::hir::def_id::{DefId, LocalDefId};
use rr_rustc_interface::interface::{Config, interface};
use rr_rustc_interface::middle::query::Providers;
use rr_rustc_interface::middle::query::queries::mir_borrowck::ProvidedValue;
use rr_rustc_interface::middle::{ty, util};
use rr_rustc_interface::polonius_engine::{Algorithm, Output};
use rr_rustc_interface::session::{self, EarlyDiagCtxt, Session};
use rr_rustc_interface::{errors, hir};

use rr_rustc_interface::driver::*;
use rr_rustc_interface::borrowck::provide;

struct OurCompilerCalls {
    args: Vec<String>,
}

fn get_attributes(tcx: ty::TyCtxt<'_>, def_id: DefId) -> &[hir::Attribute] {
    tcx.get_all_attrs(def_id)
}

fn get_attribute<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: DefId,
    segment1: &str,
    segment2: &str,
) -> Option<&'tcx hir::Attribute> {
    get_attributes(tcx, def_id).iter().find(|attr| match &attr {
        hir::Attribute::Unparsed(normal_attr) => match normal_attr.as_ref() {
            hir::AttrItem {
                path: hir::AttrPath { segments, .. },
                args: hir::AttrArgs::Empty,
                ..
            } => segments.len() == 2 && segments[0].as_str() == segment1 && segments[1].as_str() == segment2,
            _ => false,
        },
        _ => false,
    })
}

mod mir_storage {
    use super::*;

    // Since mir_borrowck does not have access to any other state, we need to use a
    // thread-local for storing the obtained MIR bodies.
    //
    // Note: We are using 'static lifetime here, which is in general unsound.
    // Unfortunately, that is the only lifetime allowed here. Our use is safe
    // because we cast it back to `'tcx` before using.
    thread_local! {
        static MIR_BODIES:
            RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
            RefCell::new(FxHashMap::default());
    }

    pub(crate) unsafe fn store_mir_body<'tcx>(
        _tcx: ty::TyCtxt<'tcx>,
        def_id: LocalDefId,
        body_with_facts: BodyWithBorrowckFacts<'tcx>,
    ) {
        // Safety: required to be the same tcx
        let body_with_facts: BodyWithBorrowckFacts<'static> = unsafe { mem::transmute(body_with_facts) };

        MIR_BODIES.with(|state| {
            let mut map = state.borrow_mut();
            assert!(map.insert(def_id, body_with_facts).is_none());
        });
    }

    #[expect(clippy::elidable_lifetime_names)]
    pub(crate) unsafe fn retrieve_mir_body<'tcx>(
        _tcx: ty::TyCtxt<'tcx>,
        def_id: LocalDefId,
    ) -> BodyWithBorrowckFacts<'tcx> {
        let body_with_facts: BodyWithBorrowckFacts<'static> = MIR_BODIES.with(|state| {
            let mut map = state.borrow_mut();
            map.remove(&def_id).unwrap()
        });

        // Safety: this is the same tcx
        unsafe { mem::transmute(body_with_facts) }
    }
}

#[expect(clippy::elidable_lifetime_names)]
fn mir_borrowck<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: LocalDefId) -> ProvidedValue<'tcx> {
    let bodies_with_facts =
        consumers::get_bodies_with_borrowck_facts(tcx, def_id, consumers::ConsumerOptions::PoloniusOutputFacts);

    for (did, body) in bodies_with_facts {
        // SAFETY: This is safe because we are feeding in the same `tcx` that is
        // going to be used as a witness when pulling out the data.
        unsafe {
            mir_storage::store_mir_body(tcx, did, body);
        }
    }
    let mut providers = Providers::default();
    provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn override_queries(_session: &Session, local: &mut util::Providers) {
    local.mir_borrowck = mir_borrowck;
}

impl Callbacks for OurCompilerCalls {
    // In this callback we override the mir_borrowck query.
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(override_queries);
    }

    fn after_analysis(&mut self, compiler: &interface::Compiler, tcx: ty::TyCtxt<'_>) -> Compilation {
        let abstract_domain: &str = self
            .args
            .iter()
            .filter(|a| a.starts_with("--analysis"))
            .flat_map(|a| a.rsplit('='))
            .next()
            .expect("Please add --analysis=<DOMAIN>");

        println!(
            "Analyzing file {} using {}...",
            compiler.sess.io.input.source_name().prefer_local(),
            abstract_domain
        );

        // collect all functions with attribute #[analyzer::run]
        let mut local_def_ids: Vec<_> = tcx
            .mir_keys(())
            .iter()
            .filter(|id| get_attribute(tcx, id.to_def_id(), "analyzer", "run").is_some())
            .collect();

        // sort according to argument span to ensure deterministic output
        local_def_ids
            .sort_unstable_by_key(|id| get_attribute(tcx, id.to_def_id(), "analyzer", "run").unwrap().span());

        for &local_def_id in local_def_ids {
            println!("Result for function {}():", tcx.item_name(local_def_id.to_def_id()));

            // SAFETY: This is safe because we are feeding in the same `tcx`
            // that was used to store the data.
            let mut body_with_facts = unsafe { mir_storage::retrieve_mir_body(tcx, local_def_id) };
            body_with_facts.output_facts = Some(Box::new(Output::compute(
                body_with_facts.input_facts.as_ref().unwrap(),
                Algorithm::Naive,
                true,
            )));
            assert!(!body_with_facts.input_facts.as_ref().unwrap().cfg_edge.is_empty());
            let body = &body_with_facts.body;

            match abstract_domain {
                "DefinitelyInitializedAnalysis" => {
                    let result = DefinitelyInitializedAnalysis::new(tcx, local_def_id.to_def_id(), body)
                        .run_fwd_analysis();
                    match result {
                        Ok(state) => {
                            println!("{}", serde_json::to_string_pretty(&state).unwrap());
                        },
                        Err(e) => eprintln!("{}", e.to_pretty_str(body)),
                    }
                },
                _ => panic!("Unknown domain argument: {abstract_domain}"),
            }
        }

        Compilation::Stop
    }
}

/// Run an analysis by calling like it rustc
///
/// Give arguments to the analyzer by prefixing them with '--analysis'
/// A abstract domain has to be provided by using '--analysis=' (without spaces), e.g.:
/// --analysis=ReachingDefsState or --analysis=DefinitelyInitializedAnalysis
fn main() {
    env_logger::init();
    let error_handler = EarlyDiagCtxt::new(session::config::ErrorOutputType::HumanReadable {
        kind: errors::emitter::HumanReadableErrorType::Default,
        color_config: errors::emitter::ColorConfig::Auto,
    });
    init_rustc_env_logger(&error_handler);
    let mut compiler_args = Vec::new();
    let mut callback_args = Vec::new();
    for arg in env::args() {
        if arg.starts_with("--analysis") {
            callback_args.push(arg);
        } else {
            compiler_args.push(arg);
        }
    }

    compiler_args.push("-Zpolonius".to_owned());
    compiler_args.push("-Zalways-encode-mir".to_owned());
    compiler_args.push("-Zcrate-attr=feature(register_tool)".to_owned());
    compiler_args.push("-Zcrate-attr=register_tool(analyzer)".to_owned());

    let mut callbacks = OurCompilerCalls {
        args: callback_args,
    };
    // Invoke compiler, and handle return code.
    let exit_code = catch_with_exit_code(move || {
        run_compiler(&compiler_args, &mut callbacks);
    });
    process::exit(exit_code)
}
