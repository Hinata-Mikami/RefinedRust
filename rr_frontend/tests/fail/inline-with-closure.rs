//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]

#[rr::inline]
fn inline_with_closure(x: i32) -> i32 {
    let identity = |y| y;
    identity(x)
}

fn main() {}
