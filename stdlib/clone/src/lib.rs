#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.clone")]
#![allow(unused)]

#[rr::export_as(core::clone::Clone)]
pub trait Clone: Sized {
    #[rr::returns("self")]
    fn clone(&self) -> Self;

    #[rr::observe("self.ghost": "source")]
    fn clone_from(&mut self, source: &Self);
}
