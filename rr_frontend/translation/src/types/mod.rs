// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utilities for translating Rust types into `RefinedRust` types.

mod local;
pub mod scope;
mod translator;
mod tyvars;

use std::fmt::Write;

pub use local::{normalize_erasing_regions_in_function, normalize_in_function, LocalTX};
/// We export these parts of the private modules
use rr_rustc_interface::middle::ty;
pub use scope::{generate_args_inst_key, GenericsKey};
pub use translator::{AdtState, CalleeState, FunctionState, STInner, TraitState, ST, TX};

use crate::base::*;

/// Mangle a name by appending type parameters to it.
pub fn mangle_name_with_tys(method_name: &str, args: &[ty::Ty<'_>]) -> String {
    // TODO: maybe come up with some better way to generate names
    let mut mangled_name = method_name.to_owned();
    for arg in args {
        mangled_name.push_str(format!("_{}", arg).as_str());
    }
    strip_coq_ident(&mangled_name)
}

/// Mangle a name by appending generic args to it.
pub fn mangle_name_with_args(name: &str, args: &[ty::GenericArg<'_>]) -> String {
    let mut mangled_base = name.to_owned();
    for arg in args {
        if let ty::GenericArgKind::Type(ty) = arg.unpack() {
            write!(mangled_base, "_{}", strip_coq_ident(&format!("{ty}"))).unwrap();
        }
    }
    mangled_base
}
