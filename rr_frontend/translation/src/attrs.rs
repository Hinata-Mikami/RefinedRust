// © 2023, The RefinedRust Develcpers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utility functions for obtaining relevant attributes.

use std::collections::HashSet;

use rr_rustc_interface::hir;
use rr_rustc_interface::span::Span;

#[derive(Debug, Clone, Copy)]
pub(crate) struct UnexpectedAttr<'a> {
    pub(crate) name: &'a str,
    pub(crate) span: Span,
}

/// Check if `<tool>::<name>` is among the attributes, where `tool` is determined by the
/// `spec_hotword` config.
/// Any arguments of the attribute are ignored.
pub(crate) fn has_tool_attr(attrs: impl IntoIterator<Item = &hir::Attribute>, name: &str) -> bool {
    get_tool_attr(attrs, name).is_some()
}

/// Get the arguments for a tool attribute, if it exists.
pub(crate) fn get_tool_attr<'a>(
    attrs: impl IntoIterator<Item = &'a hir::Attribute>,
    name: &str,
) -> Option<&'a hir::AttrArgs> {
    attrs.into_iter().find_map(|attr| match &attr {
        hir::Attribute::Unparsed(na) => {
            let segments = &na.path.segments;
            let args = &na.args;
            (segments.len() == 2
                && segments[0].as_str() == rrconfig::spec_hotword().as_str()
                && segments[1].as_str() == name)
                .then_some(args)
        },
        _ => None,
    })
}

/// Check if `<tool>::name` is among the filtered attributes.
pub(crate) fn has_tool_attr_filtered(attrs: &[&hir::AttrItem], name: &str) -> bool {
    attrs.iter().any(|item| {
        let segments = &item.path.segments;
        segments.len() == 2
            && segments[0].as_str() == rrconfig::spec_hotword().as_str()
            && segments[1].as_str() == name
    })
}

/// Check if any attribute starting with `<tool>` is among the attributes.
pub(crate) fn has_any_tool_attr(attrs: impl IntoIterator<Item = &hir::Attribute>) -> bool {
    attrs.into_iter().any(|attr| match &attr {
        hir::Attribute::Unparsed(na) => {
            let segments = &na.path.segments;
            segments[0].as_str() == rrconfig::spec_hotword().as_str()
        },
        _ => false,
    })
}

/// Get all tool attributes, i.e. attributes of the shape `<tool>::attr`, where `tool` is
/// determined by the `spec_hotword` config.
pub(crate) fn filter_for_tool<'a>(
    attrs: impl IntoIterator<Item = &'a hir::Attribute>,
) -> Vec<&'a hir::AttrItem> {
    attrs
        .into_iter()
        .filter_map(|attr| match &attr {
            hir::Attribute::Unparsed(na) => {
                let seg = na.path.segments.first()?;

                (seg.as_str() == rrconfig::spec_hotword()).then_some(na.as_ref())
            },
            _ => None,
        })
        .collect()
}

pub(crate) fn get_tool_attr_name(attr: &hir::AttrItem) -> Option<&str> {
    let segments = &attr.path.segments;
    (segments.len() == 2 && segments[0].as_str() == rrconfig::spec_hotword().as_str())
        .then(|| segments[1].as_str())
}

pub(crate) fn check_tool_attrs<'a>(
    attrs: &[&'a hir::AttrItem],
    accepted: impl IntoIterator<Item = &'a str>,
) -> Result<(), UnexpectedAttr<'a>> {
    check_tool_attr_names(
        attrs.iter().filter_map(|attr| get_tool_attr_name(attr).map(|name| (name, attr.span))),
        accepted,
    )
}

fn check_tool_attr_names<'a>(
    attrs: impl IntoIterator<Item = (&'a str, Span)>,
    accepted: impl IntoIterator<Item = &'a str>,
) -> Result<(), UnexpectedAttr<'a>> {
    let accepted: HashSet<&str> = accepted.into_iter().collect();

    for (name, span) in attrs {
        if !accepted.contains(name) {
            return Err(UnexpectedAttr { name, span });
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use rr_rustc_interface::span::{BytePos, SyntaxContext};

    use super::*;

    fn make_span(lo: u32, hi: u32) -> Span {
        Span::new(BytePos(lo), BytePos(hi), SyntaxContext::root(), None)
    }

    #[test]
    fn accepts_attr_claimed_by_any_relevant_parser() {
        let res = check_tool_attr_names([("derive_instantiate", make_span(1, 2))], [
            "derive_instantiate",
            "refined_by",
        ]);

        assert!(res.is_ok());
    }

    #[test]
    fn rejects_unclaimed_tool_attr() {
        let span = make_span(3, 4);
        let err =
            check_tool_attr_names([("mystery", span)], ["derive_instantiate", "refined_by"]).unwrap_err();

        assert_eq!(err.name, "mystery");
        assert_eq!(err.span.lo(), BytePos(3));
        assert_eq!(err.span.hi(), BytePos(4));
    }
}
