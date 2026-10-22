//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]

#[rr::may_unwind_if("True", "False")]
fn main() {}
