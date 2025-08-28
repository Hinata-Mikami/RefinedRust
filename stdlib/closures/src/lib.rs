#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.closures")]

#[rr::export_as(core::marker::Tuple)]
pub trait Tuple { }

/*
#[rr::export_as(core::ops::Fn)]
pub trait Fn<Args: Tuple>: FnMut<Args> {

    /// Performs the call operation.
    fn call(&self, args: Args) -> Self::Output;
}

#[rr::export_as(core::ops::FnMut)]
pub trait FnMut<Args: Tuple>: FnOnce<Args> {
    /// Performs the call operation.
    fn call_mut(&mut self, args: Args) -> Self::Output;
}
*/

/*
#[rr::export_as(core::ops::FnOnce)]
pub trait FnOnce<Args> {
    /// The returned type after the call operator is used.
    type Output;

    /// Performs the call operation.
    #[rr::params("m", "x")]
    #[rr::args("m", "x")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn call_once(self, args: Args) -> Self::Output;
}
*/

#[rr::export_as(core::ops::FnOnce)]
#[rr::exists("Pre" : "{xt_of Self} → {xt_of Args} → iProp Σ")]
#[rr::exists("Post" : "{xt_of Self} → {xt_of Args} → {xt_of Output} → iProp Σ")]
#[rr::nondependent]
pub trait FnOnce<Args> {
    /// The returned type after the call operator is used.
    type Output;

    /// Performs the call operation.
    #[rr::requires(#iris "{Pre} self args")]
    #[rr::ensures(#iris "{Post} self args ret")]
    fn call_once(self, args: Args) -> Self::Output;
}

#[rr::export_as(core::ops::FnMut)]
// Note: the relation gets both the current and the next state
#[rr::exists("PostMut" : "{xt_of Self} → {xt_of Args} → {xt_of Self} → {xt_of Self::Output} → iProp Σ")]
#[rr::nondependent]
pub trait FnMut<Args>: FnOnce<Args> {
    /// Performs the call operation.
    #[rr::requires(#iris "{Self::Pre} self.cur args")]
    #[rr::exists("m'")]
    #[rr::ensures(#iris "{PostMut} self.cur args m' ret")]
    #[rr::observe("self.ghost": "$# m'")]
    fn call_mut(&mut self, args: Args) -> Self::Output;
}

#[rr::export_as(core::ops::Fn)]
#[rr::nondependent]
pub trait Fn<Args>: FnMut<Args> {
    /// Performs the call operation.
    #[rr::requires(#iris "{Self::Pre} self args")]
    #[rr::ensures(#iris "{Self::Post} self args ret")]
    fn call(&self, args: Args) -> Self::Output;
}
