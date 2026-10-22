//@check-pass
#![feature(custom_inner_attributes)]
#![feature(register_tool)]
#![allow(dead_code)]
#![register_tool(rr)]
#![rr::package("long_associated_trait_bound_chain")]

trait T0 {
    type Next: T1;
}
trait T1 {
    type Next: T2;
}
trait T2 {
    type Next: T3;
}
trait T3 {
    type Next: T4;
}
trait T4 {
    type Next: T5;
}
trait T5 {
    type Next: T6;
}
trait T6 {
    type Next: T7;
}
trait T7 {
    type Next: T8;
}
trait T8 {
    type Next: T9;
}
trait T9 {
    type Next: T10;
}
trait T10 {
    type Next: T11;
}
trait T11 {}

#[rr::verify]
fn accepts_long_chain<T: T0>() {}

fn main() {}
