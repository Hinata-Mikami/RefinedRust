#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.option")]

#![rr::include("closures")]
#![rr::include("clone")]
#![rr::include("result")]

use core::mem;
use std::hint;

#[rr::refined_by("option (place_rfn {rt_of T})")]
#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind}")]
#[rr::export_as(core::option::Option)]
#[derive(Copy, Clone, Debug)]
pub enum Option<T> {
    #[rr::pattern("None")]
    #[rr::export_as(core::option::Option::None)]
    None,
    #[rr::pattern("Some" $ "x")]
    #[rr::refinement("*[x]")]
    #[rr::export_as(core::option::Option::Some)]
    Some(T)
}
use crate::Option::*;

#[rr::export_as(core::option::Option)]
impl<T> Option<T> {

    #[rr::returns("bool_decide (is_Some self)")]
    pub fn is_some(&self) -> bool {
        matches!(*self, Some(_))
    }

    #[rr::returns("bool_decide (¬ is_Some self)")]
    pub fn is_none(&self) -> bool {
        !self.is_some()
    }

    /// # Safety
    /// See stdlib
    #[rr::only_spec]
    #[rr::requires("destruct_hint self is_Some")]
    #[rr::ensures("match self with | Some x => ret = x | None => False end")]
    pub unsafe fn unwrap_unchecked(self) -> T {
        match self {
            Some(val) => val,
            // SAFETY: the safety contract must be upheld by the caller.
            None => unsafe { hint::unreachable_unchecked() },
        }
    }

    #[rr::returns("self")]
    pub const fn as_ref(&self) -> Option<&T> {
        match *self {
            Some(ref x) => Some(x),
            None => None,
        }
    }

    #[rr::only_spec]
    #[rr::exists("γ")]
    #[rr::returns("match self.cur with Some x => Some (x, γ) | None => None end")]
    #[rr::observe("self.ghost": "match self.cur with Some _ => Some (PlaceGhost (rt := {rt_of T}) γ) | None => None end")]
    pub const fn as_mut(&mut self) -> Option<&mut T> {
        match *self {
            Some(ref mut x) => Some(x),
            None => None,
        }
    }
}

#[rr::export_as(core::option::Option)]
impl<T> Option<T> {
    #[rr::requires("destruct_hint self is_Some")]
    #[rr::ensures("match self with | Some x => ret = x | None => False end")]
    pub fn unwrap(self) -> T {
        match self {
            Some(val) => val,
            None => panic!(),
        }
    }

    #[rr::returns("default def self")]
    #[rr::may_unwind_if("is_Some self ∧ {T::DropGlueUnwind}")]
    pub fn unwrap_or(self, def: T) -> T {
        match self {
            Some(x) => x,
            None => def,
        }
    }

    #[rr::returns("match self with | Some x => Ok x | None => Err err end")]
    #[rr::may_unwind_if("is_Some self ∧ {E::DropGlueUnwind}")]
    pub fn ok_or<E>(self, err: E) -> Result<T, E> {
        match self {
            Some(x) => Ok(x),
            None => Err(err),
        }
    }

    #[rr::params("op")]
    #[rr::requires(#iris "if_iNone self (⌜op = None⌝)")]
    #[rr::ensures(#iris "if_iNone self (⌜ret = None⌝ ∗ ty_ghost_drop {F} π ($# f))")]
    #[rr::requires(#iris "if_iSome self (λ self, ∃ p, ⌜op = Some p⌝ ∗ {F::Pre} π p f *[self])")]
    #[rr::ensures(#iris "if_iSome self (λ self, ∃ p x, ⌜op = Some p⌝ ∗ ⌜ret = Some x⌝ ∗ {F::Post} π p f *[self] x)")]
    #[rr::may_unwind_if("if_None self {F::DropGlueUnwind} ∧ if_Some self (λ x, ∃ p, op = Some p ∧ {F::UnwindCondition} f p *[x])")]
    pub fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Some(x) => Some(f(x)),
            None => None,
        }
    }

    #[rr::only_spec]
    #[rr::returns("self.cur")]
    #[rr::observe("self.ghost": "(None : option (place_rfn {rt_of T}))")]
    pub fn take(&mut self) -> Option<T> {
        // FIXME(const-hack) replace `mem::replace` by `mem::take` when the latter is const ready
        mem::replace(self, None)
    }

    // TODO: maybe ghost drop Self, too, in case pred returns false.
    #[rr::params("op")]
    #[rr::requires(#iris "if_iSome self (λ self, ∃ p, ⌜op = Some p⌝ ∗ {P::Pre} π p predicate *[self])")]
    #[rr::ensures(#iris "if_iSome ret (λ ret, ⌜self = Some ret⌝ ∗ ∃ p, ⌜op = Some p⌝ ∗ {P::Post} π p predicate *[ret] true)")]
    #[rr::ensures(#iris "if_iNone ret (if_iNone self (ty_ghost_drop {P} π ($# predicate)) ∗
                            if_iSome self (λ x, ∃ p, ⌜op = Some p⌝ ∗ {P::Post} π p predicate *[x] false))")]
    #[rr::may_unwind_if("if_None self {P::DropGlueUnwind} ∧ if_Some self (λ x, {T::DropGlueUnwind} ∨ ∃ p, op = Some p ∧ {P::UnwindCondition} predicate p *[x])")]
    pub fn filter<P>(self, predicate: P) -> Self
    where
        P: FnOnce(&T) -> bool,
    {
        if let Some(x) = self {
            if predicate(&x) {
                return Some(x);
            }
        }
        None
    }
}

#[rr::export_as(core::option::Option)]
impl<T> Option<Option<T>> {
    #[rr::returns("self ≫= id")]
    pub fn flatten(self) -> Option<T> {
        match self {
            Some(inner) => inner,
            None => None,
        }
    }
}
