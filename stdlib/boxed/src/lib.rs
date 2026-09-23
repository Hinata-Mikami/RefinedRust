#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]
#![allow(internal_features)]

#![feature(allocator_api)]
#![feature(ptr_internals)]
#![feature(layout_for_ptr)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.boxed")]

#![rr::include("sized")]
#![rr::include("alloc")]
#![rr::include("option")]
#![rr::include("rr_internal")]
#![rr::include("mem")]
#![rr::include("ptr")]
#![rr::include("ptr_advanced")]


use std::alloc::{self, Allocator, Global, Layout};
use std::marker::PhantomData;
use std::ptr::dangling;
use core::ptr::{self, Unique, NonNull};
use std::mem;


// TODO: maybe we should seal this definition at the module boundary so that there's no chance of
// the definition details leaking?

#[rr::export_as(alloc::boxed::Box)]
#[rr::refined_by("(x, a)" : "(place_rfn {rt_of T}) * (directRT {xt_of A})")]
#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind} ∨ {A::DropGlueUnwind}")]
#[rr::exists("l" : "loc")]
#[rr::inv(#iris "guarded true (l ◁ₗ[π, Owned] x @ ◁ {T})")]
// TODO: for unsized T, will need to use pointer metadata to determine the size.
#[rr::inv(#iris "{A::FreeablePerm} a l (ly_size {ly_of T})")]
#[rr::ty_lfts("ty_lfts {T}")]
#[rr::ty_wf_E("ty_wf_E {T}")]
#[rr::ghost_drop(#iris "∃ r, place_rfn_interp_owned x r ∗ ty_ghost_drop {T} π r")]
pub struct Box<T, A: Allocator = Global, >(#[rr::field("l")] Unique<T>, #[rr::field("$# a")] A);

// TODO: should be T: ?Sized
#[rr::export_as(alloc::boxed::Box)]
impl<T, A: Allocator> Box<T, A> {
    #[rr::params("b")]
    #[rr::requires(#type "raw" : "($#@{{ {rt_of T} }} b)" @ "{T}")]
    #[rr::requires(#iris "{A::FreeablePerm} alloc raw (ly_size {ly_of T})")]
    #[rr::requires("raw.(loc_a) ≠ 0")]
    #[rr::returns("(b, alloc)")]
    pub unsafe fn from_raw_in(raw: *mut T, alloc: A) -> Self {
        Box(unsafe { Unique::new_unchecked(raw) }, alloc)
    }

    #[rr::only_spec]
    #[rr::exists("l" : "loc")]
    #[rr::ensures(#type "l" : "($#@{{ {rt_of T} }} b.1)" @ "{T}")]
    #[rr::ensures(#iris "{A::FreeablePerm} b.2 l (ly_size {ly_of T})")]
    // This holds true even for ZSTs.
    #[rr::ensures("l.(loc_a) ≠ 0")]
    #[rr::returns("*[l; b.2]")]
    pub fn into_raw_with_allocator(b: Self) -> (*mut T, A) {
        // TODO: not sure how to implement since we cannot use the magic box deref here.
        unimplemented!();
        //let mut b = mem::ManuallyDrop::new(b);
        // We carefully get the raw pointer out in a way that Miri's aliasing model understands what
        // is happening: using the primitive "deref" of `Box`. In case `A` is *not* `Global`, we
        // want *no* aliasing requirements here!
        // In case `A` *is* `Global`, this does not quite have the right behavior; `into_raw`
        // works around that.
        //let ptr = &raw mut **b;
        //let alloc = unsafe { ptr::read(&b.1) };
        //(ptr, alloc)
    }

    #[rr::exists("l" : "loc")]
    #[rr::ensures(#type "l" : "($#@{{ {rt_of T} }} b.1)" @ "{T}")]
    #[rr::ensures(#iris "{A::FreeablePerm} b.2 l (ly_size {ly_of T})")]
    #[rr::ensures("l.(loc_a) ≠ 0")]
    #[rr::returns("*[l; b.2]")]
    pub fn into_non_null_with_allocator(b: Self) -> (NonNull<T>, A) {
        let (ptr, alloc) = Box::into_raw_with_allocator(b);
        // SAFETY: `Box` is guaranteed to be non-null.
        unsafe { (NonNull::new_unchecked(ptr), alloc) }
    }

}

    
#[rr::export_as(alloc::boxed::Box)]
#[rr::only_spec]
impl<T, A: Allocator> Box<T, A> {

    #[rr::returns("(x, alloc)")]
    pub fn new_in(x: T, alloc: A) -> Self
    where
        A: Allocator,
    {
        unimplemented!();
        //let mut boxed = Self::new_uninit_in(alloc);
        //boxed.write(x);
        //unsafe { boxed.assume_init() }
    }

    /*
    pub fn try_new_in(x: T, alloc: A) -> Result<Self, AllocError>
    where
        A: Allocator,
    {
        let mut boxed = Self::try_new_uninit_in(alloc)?;
        boxed.write(x);
        unsafe { Ok(boxed.assume_init()) }
    }

    pub fn new_uninit_in(alloc: A) -> Box<mem::MaybeUninit<T>, A>
    where
        A: Allocator,
    {
        let layout = Layout::new::<mem::MaybeUninit<T>>();
        // NOTE: Prefer match over unwrap_or_else since closure sometimes not inlineable.
        // That would make code size bigger.
        match Box::try_new_uninit_in(alloc) {
            Ok(m) => m,
            Err(_) => handle_alloc_error(layout),
        }
    }

    pub fn try_new_uninit_in(alloc: A) -> Result<Box<mem::MaybeUninit<T>, A>, AllocError>
    where
        A: Allocator,
    {
        let ptr = if T::IS_ZST {
            NonNull::dangling()
        } else {
            let layout = Layout::new::<mem::MaybeUninit<T>>();
            alloc.allocate(layout)?.cast()
        };
        unsafe { Ok(Box::from_raw_in(ptr.as_ptr(), alloc)) }
    }
    */
}

// NB: Only works for sized T.
#[rr::returns("(x, tt)")]
fn box_new<T>(x: T) -> Box<T> {
    if core::mem::size_of::<T>() == 0 {
        let ptr = std::ptr::dangling::<T>() as *mut T;
        unsafe {
            ptr.write(x);
        }
        Box(unsafe { Unique::new_unchecked(ptr) }, Global)
    } else {
        let layout = Layout::new::<T>();
        let ptr = unsafe { alloc::alloc(layout) };
        let ptr = ptr as *mut T;
        unsafe {
            ptr.write(x);
        };
        Box(unsafe { Unique::new_unchecked(ptr) }, Global)
    }
}

#[rr::export_as(alloc::boxed::Box)]
impl<T> Box<T> {
    #[rr::returns("(x, tt)")]
    pub fn new(x: T) -> Self {
        box_new(x)
    }
}

// TODO: may_dangle
#[rr::only_spec]
impl<T, A: Allocator> Drop for Box<T, A> {
    // the T in the Box is dropped by the compiler before the destructor is run

    #[rr::params("l", "lmem", "a")]
    #[rr::args("l" @ "alias_ref_t")]
    #[rr::requires(#type "l" : "-[#lmem; #($# a)]" @ "Box_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::requires(#type "lmem" : "()" @ "uninit {st_of T}")]
    #[rr::requires(#iris "{A::FreeablePerm} a lmem (ly_size {ly_of T})")]
    #[rr::ensures(#type "l" : "-[#lmem; #($# a)]" @ "Box_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    fn drop(&mut self) {
        let ptr = self.0;

        unsafe {
            let layout = Layout::for_value_raw(ptr.as_ptr());
            if layout.size() != 0 {
                self.1.deallocate(From::from(ptr.cast()), layout);
            }
        }
    }
}


#[rr::export_as(alloc::boxed::Box)]
// TODO: should be T: ?Sized
impl<T> Box<T> {
    

    #[rr::only_spec]
    #[rr::exists("l" : "loc")]
    #[rr::ensures(#type "l" : "($#@{{ {rt_of T} }} (b.1))" @ "{T}")]
    #[rr::ensures(#iris "freeable_nz l (ly_size {ly_of T}) 1 HeapAlloc")]
    // This holds true even for ZSTs.
    #[rr::ensures("l.(loc_a) ≠ 0")]
    #[rr::returns("l")]
    pub fn into_raw(b: Self) -> *mut T {
        // TODO: not sure how to implement since we cannot use the magic box deref here.
        unimplemented!();
        // Avoid `into_raw_with_allocator` as that interacts poorly with Miri's Stacked Borrows.
        //let mut b = mem::ManuallyDrop::new(b);
        // We go through the built-in deref for `Box`, which is crucial for Miri to recognize this
        // operation for it's alias tracking.
        //&raw mut **b
    }

    #[rr::params("b")]
    #[rr::requires(#type "raw" : "($#@{{ {rt_of T} }} b)" @ "{T}")]
    #[rr::requires(#iris "freeable_nz raw (ly_size {ly_of T}) 1 HeapAlloc")]
    #[rr::requires("raw.(loc_a) ≠ 0")]
    #[rr::returns("(b, tt)")]
    pub unsafe fn from_raw(raw: *mut T) -> Self {
        unsafe {
            Box::from_raw_in(raw, Global)
        }
    }
    
    #[rr::exists("l" : "loc")]
    #[rr::ensures(#type "l" : "($#@{{ {rt_of T} }} b.1)" @ "{T}")]
    #[rr::ensures(#iris "freeable_nz l (ly_size {ly_of T}) 1 HeapAlloc")]
    #[rr::ensures("l.(loc_a) ≠ 0")]
    #[rr::returns("l")]
    pub fn into_non_null(b: Self) -> NonNull<T> {
        // SAFETY: `Box` is guaranteed to be non-null.
        unsafe { NonNull::new_unchecked(Self::into_raw(b)) }
    }
}
