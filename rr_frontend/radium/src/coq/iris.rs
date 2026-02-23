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

use crate::coq::{binder, term};
use crate::fmt_list;

fn fmt_with_op(op: &str, v: &[IProp]) -> String {
    if v.is_empty() {
        return "True".to_owned();
    }

    fmt_list!(v, &format!("\n{op} "), "({})")
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Display)]
pub enum IProp {
    #[display("True")]
    True,

    #[display("{}", _0)]
    Atom(String),

    #[display("⌜({})%Z⌝", _0)]
    Pure(Box<term::Term>),

    #[display("{}", fmt_with_op("∗", _0))]
    Sep(Vec<Self>),

    #[display("{}", fmt_with_op("∨", _0))]
    Disj(Vec<Self>),

    #[display("{}", fmt_with_op("∧", _0))]
    Conj(Vec<Self>),

    #[display("{} -∗ {}", _0, _1)]
    Wand(Box<Self>, Box<Self>),

    #[display("{}{}", term::fmt_binders("∃", _0), _1)]
    Exists(binder::BinderList, Box<Self>),

    #[display("{}{}", term::fmt_binders("∀", _0), _1)]
    All(binder::BinderList, Box<Self>),
}

impl IProp {
    pub fn try_to_pure(&self) -> Option<term::Term> {
        match self {
            Self::True => Some(term::Term::Literal("True".to_owned())),
            Self::Pure(term) => Some(term.as_ref().to_owned()),
            Self::Sep(props) | Self::Conj(props) => {
                let props: Vec<_> = props.iter().map(Self::try_to_pure).try_collect()?;
                Some(term::Term::Infix("∧".to_owned(), props))
            },
            Self::Disj(props) => {
                let props: Vec<_> = props.iter().map(Self::try_to_pure).try_collect()?;
                Some(term::Term::Infix("∨".to_owned(), props))
            },
            // don't lift over existential quantifiers for now, as the RR sidecondition solver does
            // not instantiate existentials
            //Self::Exists(binders, prop) => {
            //let prop = prop.try_to_pure()?;
            //Some(term::Term::Exists(binders.to_owned(), Box::new(prop)))
            //},
            Self::All(binders, prop) => {
                let prop = prop.try_to_pure()?;
                Some(term::Term::All(binders.to_owned(), Box::new(prop)))
            },
            _ => None,
        }
    }

    #[must_use]
    pub fn purify(self) -> Self {
        if let Some(t) = self.try_to_pure() { Self::Pure(Box::new(t)) } else { self }
    }
}
