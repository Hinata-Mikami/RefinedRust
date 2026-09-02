//@check-pass
#![feature(custom_inner_attributes)]
#![feature(register_tool)]
#![allow(dead_code)]
#![register_tool(rr)]
#![rr::package("nested_hrtb_associated_trait_bound")]

trait Inner<'a, 'b> {}

trait Outer<'a> {
    type Assoc: for<'b> Inner<'a, 'b>;
}

#[rr::verify]
fn accepts_nested_hrtb<T>()
where
    for<'a> T: Outer<'a>,
{
}

fn main() {}
