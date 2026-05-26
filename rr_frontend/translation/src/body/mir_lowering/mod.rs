// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Reusable lowering from Rust MIR expressions into Caesium expressions.
//!
//! The traits in this module separate MIR expression lowering from the stateful translation of a
//! particular `RefinedRust` function body. `MirTranslationCtx` provides the shared view of the MIR body,
//! rustc context, local names, and procedure-use bookkeeping that lowering needs. `MirTypeTranslation`
//! abstracts over type-layout queries and construction of Caesium syntactic types. The extension traits
//! for places, constants, and rvalues build on those two context traits and provide default lowering
//! routines for MIR fragments.
//!
//! Function translation can implement these traits for its own context type and override the hooks that
//! depend on function-specific state, such as translating function constants, static references, borrow
//! annotations, or remapping source MIR constructs to drop-elaborated MIR. This keeps common MIR lowering
//! available to other body translators without requiring them to reuse the full normal-function `TX`.

mod call;
mod constants;
mod ctx;
mod drops;
mod place;
mod rvalue;

pub(crate) use call::{ProcedureInst, TraitMethodUseData, make_trait_method_use_data};
pub(crate) use constants::MirConstantTranslation;
pub(crate) use ctx::{MirTranslationCtx, MirTypeTranslation, TranslationKey};
pub(crate) use drops::{MirDropTranslation, make_virtual_drop_glue_method_for_param_from_scope};
pub(crate) use place::MirPlaceTranslation;
pub(crate) use rvalue::MirRvalueTranslation;
