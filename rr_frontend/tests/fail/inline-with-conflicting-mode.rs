//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]

#[rr::inline]
#[rr::trust_me]
fn conflicting_modes(x: i32) -> i32 {
    x
}

fn main() {}
