//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]
#![allow(dead_code)]

#[rr::raw_mut_self]
unsafe fn free_function(_: &mut Value) {}

struct Value;

impl Value {
    #[rr::raw_mut_self]
    fn safe_method(&mut self) {}

    #[rr::raw_mut_self]
    unsafe fn shared_receiver(&self) {}

    #[rr::raw_mut_self("argument")]
    unsafe fn with_argument(&mut self) {}

    #[rr::raw_mut_self]
    #[rr::inline]
    unsafe fn inline_method(&mut self) {}
}

trait Trait {
    #[rr::raw_mut_self]
    unsafe fn trait_method(&mut self) {}
}

impl Trait for Value {
    #[rr::raw_mut_self]
    unsafe fn trait_method(&mut self) {}
}

fn main() {}
