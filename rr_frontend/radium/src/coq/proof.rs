// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [proof mode].
//!
//! [proof mode]: https://coq.inria.fr/doc/v8.20/refman/proofs/writing-proofs/proof-mode.html#proof-mode

use std::fmt;

use derive_more::Display;
use indent_write::fmt::IndentWriter;
use indent_write::indentable::Indentable;

use crate::{coq, BASE_INDENT};

/// The [`Proof`], or [`Proof using`] command.
///
/// [`Proof`]: https://coq.inria.fr/doc/v8.20/refman/proofs/writing-proofs/proof-mode.html#coq:cmd.Proof
/// [`Proof using`]: https://rocq-prover.org/doc/v8.20/refman/proofs/writing-proofs/proof-mode.html#coq:cmd.Proof-using
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Proof {
    pub using: Option<String>,
    pub proof: coq::ProofDocument,
    pub terminator: Terminator,
}

impl Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(using) = &self.using {
            writeln!(f, "Proof using {}.", using)?;
        } else {
            writeln!(f, "Proof.")?;
        }

        write!(f, "{}", (&self.proof).indented(BASE_INDENT))?;
        writeln!(f, "{}.", self.terminator)
    }
}

/// A proof terminator, [exiting the proof state].
///
/// [exiting the proof state]: https://coq.inria.fr/doc/v8.20/refman/proofs/writing-proofs/proof-mode.html#entering-and-exiting-proof-mode
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Terminator {
    /// The [`Admitted`] command.
    ///
    /// [`Admitted`]: https://coq.inria.fr/doc/v8.20/refman/proofs/writing-proofs/proof-mode.html#coq:cmd.Admitted
    #[display("Admitted")]
    Admitted,

    /// The [`Defined`] command.
    ///
    /// [`Defined`]: https://coq.inria.fr/doc/v8.20/refman/proofs/writing-proofs/proof-mode.html#coq:cmd.Defined
    #[display("Defined")]
    Defined,

    /// The [`Qed`] command.
    ///
    /// [`Qed`]: https://coq.inria.fr/doc/v8.20/refman/proofs/writing-proofs/proof-mode.html#coq:cmd.Qed
    #[display("Qed")]
    Qed,
}
