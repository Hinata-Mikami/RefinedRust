//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]

#[rr::may_panic_if(true)]
fn main() {}
