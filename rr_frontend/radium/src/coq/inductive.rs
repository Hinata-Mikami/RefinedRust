// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [inductive] section.
//!
//! [inductive]: https://rocq-prover.org/doc/v8.20/refman/language/core/inductive.html#inductive-types-and-recursive-functions

use derive_more::{Constructor, Display};
use indent_write::indentable::Indentable as _;

use crate::coq::binder;
use crate::{BASE_INDENT, fmt_list};

/// An [Inductive] type.
///
/// [`Inductive`]: https://rocq-prover.org/doc/v8.20/refman/language/core/inductive.html#inductive-types
#[derive(Clone, Eq, PartialEq, Debug, Display, Constructor)]
#[display("Inductive {} {} :=\n{}.\n",
    name,
    parameters,
    fmt_list!(variants, "\n| ").indented(BASE_INDENT)
)]
pub struct Inductive {
    name: String,
    parameters: binder::BinderList,
    variants: Vec<Variant>,
}

impl Inductive {
    #[must_use]
    pub const fn get_name(&self) -> &String {
        &self.name
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{} {}", name, fmt_list!(params, " "))]
pub struct Variant {
    name: String,
    params: Vec<binder::Binder>,
}

impl Variant {
    #[must_use]
    pub const fn new(name: String, params: Vec<binder::Binder>) -> Self {
        Self { name, params }
    }
}
