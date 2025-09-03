#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.result")]
#![allow(unused)]

#![rr::import("rrstd.result.theories", "result")]

use std::marker::PhantomData;
use std::hint;

#[rr::export_as(core::result::Result)]
#[rr::refined_by("result (place_rfn {rt_of T}) (place_rfn {rt_of E})")]
pub enum Result<T, E> {
    #[rr::export_as(core::result::Result::Ok)]
    #[rr::pattern("Ok" $ "x")]
    #[rr::refinement("*[x]")]
    Ok(T),
    #[rr::export_as(core::result::Result::Err)]
    #[rr::pattern("Err" $ "x")]
    #[rr::refinement("*[x]")]
    Err(E),
}
use crate::Result::*;

#[rr::only_spec]
#[rr::export_as(core::result::Result)]
impl<T, E> Result<T, E> {

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("bool_decide (is_Ok x)")]
    pub fn is_ok(&self) -> bool {
        unimplemented!();
    }

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("bool_decide (is_Err x)")]
    pub fn is_err(&self) -> bool {
        unimplemented!();
    }

    #[rr::params("x")]
    #[rr::args("Ok x")]
    #[rr::returns("x")]
    pub fn unwrap(self) -> T
    where E: Debug,
    {
        match self {
            Ok(t) => t,
            Err(e) => unreachable!(),
                //unwrap_failed("called `Result::unwrap()` on an `Err` value", &e),
        }
    }

    /// # Safety
    /// See stdlib
    #[rr::params("x")]
    #[rr::args("Ok x")]
    #[rr::returns("x")]
    pub unsafe fn unwrap_unchecked(self) -> T {
        match self {
            Ok(t) => t,
            // SAFETY: the safety contract must be upheld by the caller.
            Err(_) => unsafe { hint::unreachable_unchecked() },
        }
    }
}

#[rr::export_as(core::fmt::Error)]
pub struct Error;
#[rr::export_as(core::fmt::Debug)]
pub trait Debug {
    #[rr::verify]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}

#[rr::export_as(core::fmt::Formatter)]
pub struct Formatter<'a> {
    _marker: PhantomData<&'a mut i32>,
}
