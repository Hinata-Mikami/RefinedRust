// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [LTac] section.
//!
//! [LTac]: https://rocq-prover.org/doc/v8.20/refman/proof-engine/ltac.html#ltac

use std::fmt;

use derive_more::Display;
use from_variants::FromVariants;

use crate::coq::{term, Vernac};

/// A [tactic].
///
/// [tactic]: https://rocq-prover.org/doc/v8.20/refman/coq-tacindex.html
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum LTac {
    /// TODO: To be removed - LTac<T> instead
    #[display("{}.", _0)]
    Literal(String),

    /// [`Exact`] tactic
    ///
    /// [`Exact`]: https://rocq-prover.org/doc/v8.20/refman/proof-engine/tactics.html#coq:tacn.exact
    #[display("exact {}.", _0)]
    Exact(term::Gallina),

    /// [`Let-in`] syntax
    ///
    /// [`Let-in`]: https://rocq-prover.org/doc/v8.20/refman/language/core/definitions.html#let-in-definitions
    #[display("{}", *_0)]
    #[from_variants(into)]
    LetIn(Box<LetIn>),
}

/// [`Let-in`] syntax: `let <name> := <t1> in <t2>`
///
/// [`Let-in`]: https://rocq-prover.org/doc/v8.20/refman/language/core/definitions.html#let-in-definitions
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("let {} := {} in {}", name, t1, t2)]
pub struct LetIn {
    name: String,
    t1: term::Gallina,
    t2: LTac,
}

impl LetIn {
    #[must_use]
    pub fn new(name: impl Into<String>, t1: impl Into<term::Gallina>, t2: impl Into<LTac>) -> Self {
        Self {
            name: name.into(),
            t1: t1.into(),
            t2: t2.into(),
        }
    }
}
