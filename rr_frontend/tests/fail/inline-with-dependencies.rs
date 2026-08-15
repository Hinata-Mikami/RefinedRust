//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]

#[rr::inline]
fn inline_leaf<T>(x: T) -> T {
    x
}

#[rr::inline]
fn inline_calls_inline<T>(x: T) -> T {
    inline_leaf(x)
}

fn main() {}
