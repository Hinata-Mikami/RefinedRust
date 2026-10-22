//@check-pass
#![feature(custom_inner_attributes)]
#![feature(register_tool)]
#![allow(dead_code)]
#![register_tool(rr)]
#![rr::package("filtered_trait_attribute_collision")]

#[rr::exists("DropGlueUnwind" : "Prop")]
trait CollidingDropAttribute {}

#[rr::invariant("{T::DropGlueUnwind}")]
struct UsesOrdinaryAttribute<T: CollidingDropAttribute>(T);

fn main() {}
