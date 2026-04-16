// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

pub(crate) mod signature;
mod translation;
mod mir_mapper;

pub use self::mir_mapper::{MappingResult, Origin, SourceLoc, TargetLoc, format_mapping, map_drop_elaborated_to_borrow_checked};
pub(crate) use translation::get_arg_syntypes_for_procedure_call;
