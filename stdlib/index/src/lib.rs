#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.index")]
#![allow(unused)]

#![rr::include("sized")]


#[rr::export_as(core::ops::Index)]
#[rr::exists("IndexProj" : "{xt_of Self} → {xt_of Idx} → {xt_of Output} → Prop")]
pub trait Index<Idx: ?Sized> {
    /// The returned type after indexing.
    type Output: ?Sized;

    #[rr::ensures("{IndexProj} self index ret")]
    fn index(&self, index: Idx) -> &Self::Output;
}

#[rr::export_as(core::ops::IndexMut)]
// basically needs a projection and backprojection function
#[rr::exists("IndexMutInj" : "{xt_of Self} → {xt_of Idx} → gname → {rt_of Self}")]
pub trait IndexMut<Idx: ?Sized>: Index<Idx> {
    /// Performs the mutable indexing (`container[index]`) operation.
    #[rr::exists("γi", "ret")]
    #[rr::ensures("{Self::IndexProj} self.cur index ret")]
    #[rr::returns("(ret, γi)")]
    #[rr::observe("self.ghost" : "#({IndexMutInj} self.cur index γi)")]
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
