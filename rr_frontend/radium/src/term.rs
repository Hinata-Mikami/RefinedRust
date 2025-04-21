// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Extended terms, specifically for `RefinedRust`.

use derive_more::Display;

use crate::{coq, display_list};

#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum RefinedRustType {
    /// `function_ty` type
    #[display("function_ty")]
    FunctionTy,

    /// `gname` type
    #[display("gname")]
    Gname,

    /// `layout` type
    #[display("layout")]
    Layout,

    /// `lft` type
    #[display("lft")]
    Lft,

    /// `loc` type
    #[display("loc")]
    Loc,

    /// `(place_rfn _)` type
    #[display("(place_rfn {})", &_0)]
    PlaceRfn(Box<coq::term::Type>),

    /// `(plist _ _)` type
    ///
    /// A plist with a given type constructor over a list of types
    #[display("(plist {} [{}])", _0, display_list!(_1, "; ", "{} : Type"))]
    PList(String, Vec<coq::term::Type>),

    /// `rtype` type
    #[display("rtype")]
    Rtype,

    /// `spec_with (lfts: nat) (rts: list Type) (SPEC: Type)` type
    #[display("(spec_with {} {} {})", _0, coq::term::fmt_list(_1), &_2)]
    SpecWith(usize, Vec<coq::term::Type>, Box<coq::term::Type>),

    /// `struct_layout` type
    #[display("struct_layout")]
    StructLayout,

    /// `struct_t (sls: struct_layout_spec) (tys: hlist type (list Type))` type
    #[display("(struct_t {} {})", _0, coq::term::fmt_hlist(_1))]
    StructT(coq::term::Gallina, Vec<coq::term::Type>),

    /// `syn_type` type
    #[display("syn_type")]
    SynType,

    /// `type (rt: Type)` type
    #[display("(type {})", &_0)]
    Ttype(Box<coq::term::Type>),
}

impl From<RefinedRustType> for coq::term::Type {
    fn from(ty: RefinedRustType) -> Self {
        Self::UserDefined(ty)
    }
}

impl From<Box<RefinedRustType>> for Box<coq::term::Type> {
    fn from(ty: Box<RefinedRustType>) -> Self {
        Self::new(coq::term::Type::UserDefined(*ty))
    }
}
