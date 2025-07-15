// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [LTac] section.
//!
//! [LTac]: https://rocq-prover.org/doc/v8.20/refman/proof-engine/ltac.html#ltac

use std::fmt;

use derive_more::{Display, From};

use crate::coq::term;
use crate::model;

/// A [tactic].
///
/// [tactic]: https://rocq-prover.org/doc/v8.20/refman/coq-tacindex.html
pub type LTac = RocqLTac<model::LTac>;

#[derive(Clone, Eq, PartialEq, Debug, Display, From)]
pub enum RocqLTac<T> {
    /// [`Exact`] tactic
    ///
    /// [`Exact`]: https://rocq-prover.org/doc/v8.20/refman/proof-engine/tactics.html#coq:tacn.exact
    #[display("exact {}.", _0)]
    Exact(term::Term),

    /// [`Split`] tactic
    ///
    /// [`Split`]: https://rocq-prover.org/doc/v8.20/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.split
    #[display("split.")]
    Split,

    /// [`Apply`] tactic
    ///
    /// [`Apply`]: https://rocq-prover.org/doc/v8.20/refman/proof-engine/tactics.html#coq:tacn.apply
    #[display("apply {}.", _0)]
    Apply(term::Term),

    /// [`Let-in`] syntax
    ///
    /// [`Let-in`]: https://rocq-prover.org/doc/v8.20/refman/language/core/definitions.html#let-in-definitions
    #[display("{}", *_0)]
    #[from(forward)]
    LetIn(Box<LetIn>),

    /// User defined type
    #[display("{}.", _0)]
    #[from(ignore)]
    UserDefined(T),

    /// Literal Ltac strings for backwards compatibility
    #[display("{}.", _0)]
    #[from(ignore)]
    Literal(String),
}

/// [`Let-in`] syntax: `let <name> := <t1> in <t2>`
///
/// [`Let-in`]: https://rocq-prover.org/doc/v8.20/refman/language/core/definitions.html#let-in-definitions
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("let {} := {} in {}", name, t1, t2)]
pub struct LetIn {
    name: String,
    t1: term::Term,
    t2: LTac,
}

impl LetIn {
    #[must_use]
    pub fn new<I1: Into<String>, I2: Into<term::Term>, I3: Into<LTac>>(name: I1, t1: I2, t2: I3) -> Self {
        Self {
            name: name.into(),
            t1: t1.into(),
            t2: t2.into(),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Attrs {
    pub ltac: LTac,
    pub scope: Option<Scope>,
}

impl fmt::Display for Attrs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(scope) = &self.scope {
            write!(f, "{}: ", scope)?;
        }
        write!(f, "{}", self.ltac)
    }
}

impl From<LTac> for Attrs {
    fn from(ltac: LTac) -> Self {
        Self::new(ltac)
    }
}

impl Attrs {
    #[must_use]
    pub fn new<I: Into<LTac>>(ltac: I) -> Self {
        Self {
            ltac: ltac.into(),
            scope: None,
        }
    }

    #[must_use]
    pub fn scope<I: Into<Scope>>(self, scope: I) -> Self {
        let scope = Some(scope.into());

        Self { scope, ..self }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Display)]
pub enum Scope {
    #[display("{}", _0)]
    Focus(usize),

    #[display("all")]
    All,
}
