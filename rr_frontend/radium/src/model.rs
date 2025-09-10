// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Extended Rocq definitions, specifically made for `RefinedRust`.

use derive_more::Display;

use crate::{coq, fmt_list};

#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum Term {
    /// An Iris Term
    #[display("({})%I", _0)]
    IProp(coq::iris::IProp),
}

#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
#[expect(clippy::enum_variant_names)]
pub enum Type {
    /// `function_ty` type
    #[display("function_ty")]
    FunctionTy,

    /// `gname` type
    #[display("gname")]
    Gname,

    /// `thread_id` type
    #[display("thread_id")]
    ThreadId,

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
    #[display("(place_rfnRT {})", &_0)]
    PlaceRfn(Box<coq::term::Type>),

    /// `(plist _ _)` type
    ///
    /// A plist with a given type constructor over a list of types
    #[display("(plist {} [{}])", _0, fmt_list!(_1, "; ", |x| { format!("{x} : {}", _2) }))]
    PList(String, Vec<coq::term::Type>, String),

    /// `rtype` type
    #[display("rtype")]
    Rtype,

    /// `spec_with (lfts: nat) (rts: list Type) (SPEC: Type)` type
    #[display("(spec_with {} {} ({}))", _0, coq::term::fmt_list(_1), &_2)]
    SpecWith(usize, Vec<coq::term::Type>, Box<coq::term::Type>),

    /// `struct_layout` type
    #[display("struct_layout")]
    StructLayout,

    /// `struct_t (sls: struct_layout_spec) (tys: hlist type (list Type))` type
    #[display("(struct_t {} {})", _0, coq::term::fmt_hlist(_1))]
    StructT(coq::term::Term, Vec<coq::term::Type>),

    /// `syn_type` type
    #[display("syn_type")]
    SynType,

    /// `type (rt: RT)` type
    #[display("(type {})", &_0)]
    Ttype(Box<coq::term::Type>),

    #[display("(RT_xt {})", _0)]
    RTXT(Box<coq::term::Type>),
}

impl From<Type> for coq::term::Type {
    fn from(ty: Type) -> Self {
        Self::UserDefined(ty)
    }
}

impl From<Box<Type>> for Box<coq::term::Type> {
    fn from(ty: Box<Type>) -> Self {
        Self::new(coq::term::Type::UserDefined(*ty))
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum LTac {
    #[display("print_remaining_trait_goal")]
    PrintRemainingTraitGoal,

    #[display("repeat liRStep; liShow")]
    RepeatLiRStep,

    #[display("sidecond_hammer")]
    SidecondHammer,

    #[display("sidecond_solver")]
    SidecondSolver,

    #[display("solve_inhabited")]
    SolveInhabited,

    #[display("unfold {}; solve_trait_incl_prelude", _0)]
    SolveTraitInclPrelude(String),

    #[display("Unshelve")]
    Unshelve,
}

impl From<LTac> for coq::ltac::LTac {
    fn from(ty: LTac) -> Self {
        Self::UserDefined(ty)
    }
}

impl LTac {
    #[must_use]
    pub fn scope<I: Into<coq::ltac::Scope>>(self, scope: I) -> coq::ltac::Attrs {
        coq::ltac::Attrs::new(self).scope(scope)
    }
}
