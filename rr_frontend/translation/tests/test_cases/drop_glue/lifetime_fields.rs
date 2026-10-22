#![allow(dead_code)]

use core::marker::PhantomData;

pub struct Bar<'b, U> {
    x: PhantomData<(&'b (), U)>,
}

impl<'b, U> Drop for Bar<'b, U> {
    fn drop(&mut self) {}
}

#[drop_glue::run]
pub struct Foo<'a, T> {
    x: Bar<'a, &'a T>,
}
