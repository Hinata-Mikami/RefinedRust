#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.clone")]
#![allow(unused)]

#[rr::export_as(core::clone::Clone)]
pub trait Clone: Sized {
    #[rr::returns("self")]
    fn clone(&self) -> Self;

    #[rr::observe("self.ghost": "($#@{{ {Self} }} source)")]
    fn clone_from(&mut self, source: &Self) 
    {
        *self = source.clone();
    }
}

//#[rr::export_as(core::marker::Sized)]
//pub trait Sized { }


#[rr::export_as(core::marker::Copy)]
#[rr::semantic("Copyable {Self}")]
pub trait Copy: Clone {
}

/*
// TODO: before advancing this further, handle default impls.
impl Clone for i32 { 
    #[rr::default_spec]
    fn clone(&self) -> Self {
        *self
    }
    //#[rr::default_spec]
    //fn clone_from(&mut self, source: &Self) {
        // *self = *source;
    //}
}

impl Copy for i32 { }

*/

