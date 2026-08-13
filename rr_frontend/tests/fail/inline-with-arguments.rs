//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]

#[rr::inline("argument")]
fn inline_with_argument(x: i32) -> i32 {
    x
}

fn main() {}
