// © 2023, The RefinedRust Develcpers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Utility functions for obtaining relevant attributes.

use rr_rustc_interface::ast;

/// Check if `<tool>::<name>` is among the attributes, where `tool` is determined by the
/// `spec_hotword` config.
/// Any arguments of the attribute are ignored.
pub fn has_tool_attr(attrs: &[ast::ast::Attribute], name: &str) -> bool {
    get_tool_attr(attrs, name).is_some()
}

/// Get the arguments for a tool attribute, if it exists.
pub fn get_tool_attr<'a>(attrs: &'a [ast::ast::Attribute], name: &str) -> Option<&'a ast::ast::AttrArgs> {
    attrs.iter().find_map(|attr| match &attr.kind {
        ast::ast::AttrKind::Normal(na) => {
            let segments = &na.item.path.segments;
            let args = &na.item.args;
            (segments.len() == 2
                && segments[0].ident.as_str() == rrconfig::spec_hotword().as_str()
                && segments[1].ident.as_str() == name)
                .then_some(args)
        },
        _ => None,
    })
}

/// Check if `<tool>::name` is among the filtered attributes.
pub fn has_tool_attr_filtered(attrs: &[&ast::ast::AttrItem], name: &str) -> bool {
    attrs.iter().any(|item| {
        let segments = &item.path.segments;
        segments.len() == 2
            && segments[0].ident.as_str() == rrconfig::spec_hotword().as_str()
            && segments[1].ident.as_str() == name
    })
}

/// Check if any attribute starting with `<tool>` is among the attributes.
pub fn has_any_tool_attr(attrs: &[ast::ast::Attribute]) -> bool {
    attrs.iter().any(|attr| match &attr.kind {
        ast::ast::AttrKind::Normal(na) => {
            let segments = &na.item.path.segments;
            segments[0].ident.as_str() == rrconfig::spec_hotword().as_str()
        },
        _ => false,
    })
}

/// Get all tool attributes, i.e. attributes of the shape `<tool>::attr`, where `tool` is
/// determined by the `spec_hotword` config.
pub fn filter_for_tool(attrs: &[ast::ast::Attribute]) -> Vec<&ast::ast::AttrItem> {
    attrs
        .iter()
        .filter_map(|attr| match &attr.kind {
            ast::ast::AttrKind::Normal(na) => {
                let item = &na.item;

                let seg = item.path.segments.first()?;

                (seg.ident.name.as_str() == rrconfig::spec_hotword()).then_some(item)
            },
            _ => None,
        })
        .collect()
}
