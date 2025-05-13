// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use serde::Serialize;

/// Trait to be used to define an abstract domain by defining the type of its elements.
/// These elements can be used in the ``Analyzer`` to represent an abstraction of the concrete
/// state at program points.
///
/// To ensure that the analysis is converging to a correct fixed point implementations `S` of this
/// trait should fulfill the following properties:
/// * `join()` implicitly defines a partial order of abstraction `<=`, such that forall x,y: S :: `x <=
///   x.join(y)` && `y <= x.join(y)`; i.e. `join()` computes an upper bound in that order, which means it
///   abstracts more (or equally many) concrete states, in particular it represents all concrete states that
///   were abstracted by either `x` or `y`.
/// * The 'abstract transformers' `apply_statement_effect` and `apply_terminator_effect` should correctly
///   abstract the concrete semantics of the given operation, i.e. the resulting abstraction should represent
///   a superset of the possible concrete states after applying the statement or terminator to any of the
///   concrete states represented by the abstraction before. (If an operation is not supported an
///   `AnalysisError::UnsupportedStatement` can be returned.)
/// * `apply_terminator_effect` should assign an abstract state to every successor basic block, otherwise
///   `NoStateAfterSuccessor` error will be returned by the analysis.
///
/// To get a result that is as precise as possible implementers probably also want to fulfill the
/// following properties:
/// * `join()` should return the **least** least upper bound.
/// * The 'abstract transformers' `apply_statement_effect` and `apply_terminator_effect` should abstract the
///   concrete semantics as precise as possible.
// Sized needed for apply_terminator_effect's return type
pub trait AbstractState: Clone + Eq + Sized + Serialize {
    /// Lattice operation to join `other` into this state, producing the (least) upper bound
    fn join(&mut self, other: &Self);
}
