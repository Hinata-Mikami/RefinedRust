#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.closures")]

// NOTE: Our translation of trait requirements erases `Tuple` requirements.
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


impl<A, F: ?Sized> Fn<A> for &F
where
    F: Fn<A>,
{
    #[rr::default_spec]
    #[rr::only_spec]
    fn call(&self, args: A) -> F::Output {
        (**self).call(args)
    }
}

#[rr::instantiate("PostMut" := "λ s args s2 ret, (⌜s2 = s⌝ ∗ {F::Post} s args ret)%I")]
impl<A, F: ?Sized> FnMut<A> for &F
where
    F: Fn<A>,
{
    #[rr::default_spec]
    #[rr::only_spec]
    fn call_mut(&mut self, args: A) -> F::Output {
        (**self).call(args)
    }
}

#[rr::instantiate("Pre" := "{F::Pre}")]
#[rr::instantiate("Post" := "{F::Post}")]
impl<A, F: ?Sized> FnOnce<A> for &F
where
    F: Fn<A>,
{
    type Output = F::Output;

    #[rr::default_spec]
    #[rr::only_spec]
    fn call_once(self, args: A) -> F::Output {
        (*self).call(args)
    }
}

#[rr::instantiate("PostMut" := "λ s args s2 ret, ({F::PostMut} s.cur args s2.cur ret ∗ ⌜s.ghost = s2.ghost⌝)%I")]
impl<A, F: ?Sized> FnMut<A> for &mut F
where
    F: FnMut<A>,
{
    #[rr::default_spec]
    #[rr::only_spec]
    fn call_mut(&mut self, args: A) -> F::Output {
        (*self).call_mut(args)
    }
}

#[rr::instantiate("Pre" := "λ s args, {F::Pre} s.cur args")]
#[rr::instantiate("Post" := "λ s args ret, (∃ s2, {F::PostMut} s.cur args s2 ret ∗ gvar_pobs s.ghost ($# s2))%I")]
impl<A, F: ?Sized> FnOnce<A> for &mut F
where
    F: FnMut<A>,
{
    type Output = F::Output;

    #[rr::default_spec]
    #[rr::only_spec]
    fn call_once(self, args: A) -> F::Output {
        (*self).call_mut(args)
    }
}
