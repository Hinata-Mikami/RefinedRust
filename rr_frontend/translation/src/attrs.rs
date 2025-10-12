// © 2023, The RefinedRust Develcpers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utility functions for obtaining relevant attributes.

use rr_rustc_interface::hir;

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

                (seg.name.as_str() == rrconfig::spec_hotword()).then_some(na.as_ref())
            },
            _ => None,
        })
        .collect()
}
