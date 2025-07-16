// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [iris]-related terms and types.
//!
//! [iris]: https://iris-project.org/

// better representation of Iprops?
// - in particular for building the existential abstraction, direct support for existentials would be good.
// - DeBruijn probably not worth it, I don't need subst or anything like that. just try to keep variables
//   apart when generating them.

use derive_more::Display;

use crate::coq::binder;
use crate::display_list;

fn fmt_with_op(op: &str, v: &[IProp]) -> String {
    if v.is_empty() {
        return "True".to_owned();
    }

    display_list!(v, &format!("\n{op} "), "({})")
}

fn fmt_binders(op: &str, binders: &[binder::Binder]) -> String {
    if binders.is_empty() {
        return String::new();
    }

    format!("{} {}, ", op, display_list!(binders, " "))
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum IProp {
    #[display("True")]
    True,

    #[display("{}", _0)]
    Atom(String),

    #[display("⌜{}⌝", _0)]
    Pure(String),

    #[display("{}", fmt_with_op("∗", _0))]
    Sep(Vec<IProp>),

    #[display("{}", fmt_with_op("∨", _0))]
    Disj(Vec<IProp>),

    #[display("{}", fmt_with_op("∧", _0))]
    Conj(Vec<IProp>),

    #[display("{} -∗ {}", _0, _1)]
    Wand(Box<IProp>, Box<IProp>),

    #[display("{}{}", fmt_binders("∃", _0), _1)]
    Exists(Vec<binder::Binder>, Box<IProp>),

    #[display("{}{}", fmt_binders("∀", _0), _1)]
    All(Vec<binder::Binder>, Box<IProp>),

    // prop, name
    #[display("⌜name_hint \"{}\" ({})⌝", _1, _0)]
    PureWithName(String, String),
}

/// Representation of an Iris predicate
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{} ({})%I : iProp Σ", fmt_binders("λ", binders), prop)]
pub struct IPropPredicate {
    binders: Vec<binder::Binder>,
    prop: IProp,
}

impl IPropPredicate {
    #[must_use]
    pub const fn new(binders: Vec<binder::Binder>, prop: IProp) -> Self {
        Self { binders, prop }
    }
}
