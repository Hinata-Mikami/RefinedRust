
#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.controlflow")]
#![rr::include("option")]
#![rr::include("result")]
#![allow(unused)]

mod convert;
use convert::*;

#[rr::refined_by("sum (place_rfn {rt_of C}) (place_rfn {rt_of B})")]
#[rr::export_as(core::ops::ControlFlow)]
pub enum ControlFlow<B, C = ()> {
    #[rr::pattern("inl" $ "x")]
    #[rr::refinement("*[x]")]
    #[rr::export_as(core::ops::ControlFlow::Continue)]
    Continue(C),
    /// Exit the operation without running subsequent phases.
    #[rr::pattern("inr" $ "x")]
    #[rr::refinement("*[x]")]
    #[rr::export_as(core::ops::ControlFlow::Break)]
    Break(B),
}

#[rr::export_as(core::ops::FromResidual)]
#[rr::exists("FromResidualFn" : "{xt_of R} → option {xt_of Self}")]
pub trait FromResidual<R = <Self as Try>::Residual> {
    /// Constructs the type from a compatible `Residual` type.
    ///
    /// This should be implemented consistently with the `branch` method such
    /// that applying the `?` operator will get back an equivalent residual:
    /// `FromResidual::from_residual(r).branch() --> ControlFlow::Break(r)`.
    /// (It must not be an *identical* residual when interconversion is involved.)
    #[rr::exists("y")]
    #[rr::returns("y")]
    #[rr::ensures("Some y = {FromResidualFn} residual")]
    fn from_residual(residual: R) -> Self;
}

#[rr::export_as(core::ops::Try)]
#[rr::exists("FromOutputFn" : "{xt_of Output} → {xt_of Self}")]
#[rr::exists("BranchFn" : "{xt_of Self} → sum ({xt_of Output}) ({xt_of Residual})")]
// TODO: state the law here
// TODO: needs dep on FromResidual attrs
//#[rr::exists("BranchLaw" : "∀ x r, {Self::FromResidualFn} r = Some x → {BranchFn} x = inr r")]
pub trait Try: FromResidual {
    /// The type of the value produced by `?` when *not* short-circuiting.
    type Output;

    /// The type of the value passed to [`FromResidual::from_residual`]
    /// as part of `?` when short-circuiting.
    ///
    /// This represents the possible values of the `Self` type which are *not*
    /// represented by the `Output` type.
    type Residual;

    /// Constructs the type from its `Output` type.
    ///
    /// This should be implemented consistently with the `branch` method
    /// such that applying the `?` operator will get back the original value:
    /// `Try::from_output(x).branch() --> ControlFlow::Continue(x)`.
    #[rr::returns("{FromOutputFn} (output)")]
    fn from_output(output: Self::Output) -> Self;

    /// Used in `?` to decide whether the operator should produce a value
    /// (because this returned [`ControlFlow::Continue`])
    /// or propagate a value back to the caller
    /// (because this returned [`ControlFlow::Break`]).
    #[rr::returns("{BranchFn} (self)")]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}

#[rr::instantiate("FromOutputFn" := "λ out, Some out")]
#[rr::instantiate("BranchFn" := "λ s, match s with | Some(x) => inl(x) | None => inr(None) end")]
//#[rr::instantiate("BranchLaw" := "ltac:(naive_solver)")]
impl<T> Try for Option<T> {
    type Output = T;
    type Residual = Option<Infallible>;

    #[rr::default_spec]
    fn from_output(output: Self::Output) -> Self {
        Some(output)
    }

    #[rr::trust_me]
    #[rr::default_spec]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        }
    }
}

#[rr::instantiate("FromResidualFn" := "λ _, Some None")]
impl<T> FromResidual for Option<T> {
    #[rr::default_spec]
    fn from_residual(residual: Option<Infallible>) -> Self {
        None
    }
}


#[rr::instantiate("FromOutputFn" := "λ out, inl (out)")]
#[rr::instantiate("BranchFn" := "result_xmap id (inr)")]
impl<B, C> Try for ControlFlow<B, C> {
    type Output = C;
    type Residual = ControlFlow<B, Infallible>;

    #[rr::default_spec]
    fn from_output(output: Self::Output) -> Self {
        ControlFlow::Continue(output)
    }

    #[rr::trust_me]
    #[rr::default_spec]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            ControlFlow::Continue(c) => ControlFlow::Continue(c),
            ControlFlow::Break(b) => ControlFlow::Break(ControlFlow::Break(b)),
        }
    }
}

#[rr::instantiate("FromResidualFn" := "λ s, match s with | inl(x) => None | inr(x) => Some (inr x) end")]
// Note: manually specifying the residual type instead of using the default to work around
// https://github.com/rust-lang/rust/issues/99940
impl<B, C> FromResidual<ControlFlow<B, Infallible>> for ControlFlow<B, C> {

    #[rr::trust_me]
    #[rr::default_spec]
    fn from_residual(residual: ControlFlow<B, Infallible>) -> Self {
        match residual {
            ControlFlow::Break(b) => ControlFlow::Break(b),
            ControlFlow::Continue(i) => unreachable!(),
        }
    }
}


#[rr::instantiate("FromOutputFn" := "λ out, Ok (out)")]
#[rr::instantiate("BranchFn" := "result_xmap id (λ x, (Err x))")]
impl<T, E> Try for Result<T, E> {
    type Output = T;
    type Residual = Result<Infallible, E>;

    #[rr::default_spec]
    fn from_output(output: Self::Output) -> Self {
        Ok(output)
    }

    #[rr::trust_me]
    #[rr::default_spec]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(Err(e)),
        }
    }
}

#[rr::instantiate("FromResidualFn" := "λ s, match s with | inl(x) => None | inr(x) => Some (inr (({F::FromFn} x))) end")]
impl<T, E, F: From<E>> FromResidual<Result<Infallible, E>> for Result<T, F> {
    #[rr::trust_me]
    #[rr::default_spec]
    fn from_residual(residual: Result<Infallible, E>) -> Self {
        match residual {
            Err(e) => Err(From::from(e)),
            Ok(_) => unreachable!(),
        }
    }
}
