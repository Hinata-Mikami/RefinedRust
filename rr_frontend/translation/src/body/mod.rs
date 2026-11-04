// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

pub(crate) mod drop_glue_translation;
pub(crate) mod function_translation;
pub(crate) mod mir_lowering;
pub(crate) mod panic;
pub(crate) mod signature;

pub(crate) use function_translation::get_arg_syntypes_for_procedure_call;
