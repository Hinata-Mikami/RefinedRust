// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [LTac] section.
//!
//! [LTac]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/ltac.html#ltac

use std::fmt;

use derive_more::Display;
use from_variants::FromVariants;

use crate::coq::{term, Vernac};

/// A [tactic].
///
/// [tactic]: https://coq.inria.fr/doc/v8.20/refman/coq-tacindex.html
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum LTac {
    /// Placeholder for not yet imported definitions. Will be removed.
    #[display("{}.", _0)]
    Literal(String),

    /// [`Exact`] tactic
    ///
    /// [`Exact`]: https://rocq-prover.org/doc/V8.20.1/refman/proof-engine/tactics.html#coq:tacn.exact
    #[display("exact {}.", _0)]
    Exact(term::Gallina),

    /// [`Let-in`] syntax
    ///
    /// [`Let-in`]: https://coq.inria.fr/doc/v8.20/refman/language/core/definitions.html#let-in-definitions
    #[display("{}.", *_0)]
    LetIn(Box<LetIn>),
}

/// [`Let-in`] syntax: `let <name> := <t1> in <t2>`
///
/// [`Let-in`]: https://coq.inria.fr/doc/v8.20/refman/language/core/definitions.html#let-in-definitions
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("let {} := {} in {}", name, t1, t2)]
pub struct LetIn {
    name: String,
    t1: LTac,
    t2: LTac,
}
