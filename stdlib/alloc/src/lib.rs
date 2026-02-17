#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![feature(allocator_api)]
#![feature(ptr_alignment_type)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.alloc")]
#![rr::import("rrstd.alloc.theories", "shims")]


mod layout;
use layout::*;

use std::ptr::{NonNull, copy_nonoverlapping};
use std::alloc::{AllocError};

#[rr::export_as(alloc::alloc::Global)]
pub struct Global {

}

impl Global {
    #[rr::skip]
    fn foo(&self) {

    }
}

#[rr::instantiate("FreeablePerm" := "λ _ l sz, freeable_nz l sz 1 HeapAlloc")]
unsafe impl Allocator for Global {
    //fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        //unimplemented!();
    //}

    //unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        //unimplemented!();
    //}
}

#[rr::export_as(alloc::alloc::Allocator)]
#[rr::exists("FreeablePerm" : "{xt_of Self} → loc → nat → iProp Σ")]
pub unsafe trait Allocator {
    // Required methods
    //fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;
    //unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
}


/// Allocation functions using the global allocator 

#[rr::export_as(alloc::alloc::alloc)]
#[rr::only_spec]
#[rr::requires("ly.(layout_sz) > 0")]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures(#iris "freeable_nz l ly.(layout_sz) 1 HeapAlloc")]
#[rr::ensures(#type "l" : "()" @ "uninit (UntypedSynType ly)")]
#[rr::ensures("min_alloc_start ≤ l.(loc_a) ≤ max_alloc_end")]
pub fn alloc_alloc(ly: Layout) -> *mut u8 {
    unimplemented!();
}

#[rr::export_as(alloc::alloc::dealloc)]
#[rr::only_spec]
#[rr::requires(#iris "freeable_nz ptr ly.(layout_sz) 1 HeapAlloc")]
#[rr::requires("0 < ly.(layout_sz)")]
#[rr::requires(#type "ptr" : "()" @ "uninit (UntypedSynType ly)")]
pub fn alloc_dealloc(ptr: *mut u8, ly: Layout) {
    // TODO: verify against dealloc_internal
    unimplemented!();
}


#[rr::export_as(alloc::alloc::realloc)]
#[rr::only_spec]
#[rr::params("v")]
// TODO: restriction by the spec: we cannot shrink it
#[rr::requires("(ly.(layout_sz) ≤ new_size)%Z")]
#[rr::requires("(0 < ly.(layout_sz))%Z")]
#[rr::requires("new_size ≤ MaxInt ISize")]
// TODO: restriction placed by our syntype model, not required in Rust
#[rr::requires("layout_wf (Layout (Z.to_nat new_size) (layout_alignment_log2_nat ly))")]
#[rr::requires(#type "ptr" : "v" @ "value_t (UntypedSynType ly)")]
#[rr::requires(#iris "freeable_nz ptr ly.(layout_sz) 1 HeapAlloc")]
#[rr::exists("ptr_new", "v'")]
#[rr::returns("ptr_new")]
#[rr::ensures(#iris "freeable_nz ptr_new (Z.to_nat new_size) 1 HeapAlloc")]
#[rr::ensures(#type "ptr_new" : "v ++ v' : val" @ "value_t (UntypedSynType (Layout (Z.to_nat new_size) (layout_alignment_log2_nat ly)))")]
#[rr::ensures("v' `has_layout_val` (Layout (Z.to_nat new_size - ly.(layout_sz)) (layout_alignment_log2_nat ly))")]
#[rr::ensures("min_alloc_start ≤ ptr_new.(loc_a) ≤ max_alloc_end")]
pub fn realloc(ptr: *mut u8, ly: Layout, new_size: usize) -> *mut u8 {
    // TODO: verify against realloc_internal
    unimplemented!();
}


/// Internal shims implemented against the Radium semantics
#[rr::code_shim("alloc_alloc_def")]
#[rr::requires("size ∈ ISize")]
#[rr::requires("(size > 0)%Z")]
// TODO: this restriction would not be necessary, but needed because the layout algorithm requires it. Can we lift this?
#[rr::requires("layout_wf (Layout (Z.to_nat size) (Z.to_nat align_log2))")]
#[rr::requires("ly_align_in_bounds (Layout (Z.to_nat size) (Z.to_nat align_log2))")]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures(#iris "freeable_nz l (Z.to_nat size) 1 HeapAlloc")]
#[rr::ensures(#type "l" : "()" @ "uninit (UntypedSynType (Layout (Z.to_nat size) (Z.to_nat align_log2)))")]
#[rr::ensures("min_alloc_start ≤ l.(loc_a) ≤ max_alloc_end")]
fn alloc_alloc_internal(size: usize, align_log2: usize) -> *mut u8 {
    unimplemented!();
}

#[rr::code_shim("alloc_dealloc_def")]
#[rr::requires(#iris "freeable_nz ptr (Z.to_nat size) 1 HeapAlloc")]
#[rr::requires("(0 < size)%Z")]
#[rr::requires(#type "ptr" : "()" @ "uninit (UntypedSynType (Layout (Z.to_nat size) (Z.to_nat align_log2)))")]
fn alloc_dealloc_internal(size: usize, align_log2: usize, ptr: *mut u8) {
    unimplemented!();
}

// TODO verify
#[rr::only_spec]
#[rr::params("v")]
// TODO: restriction by the spec: we cannot shrink it
#[rr::requires("(old_size ≤ new_size)%Z")]
#[rr::requires("(0 < old_size)%Z")]
#[rr::requires("new_size ≤ MaxInt ISize")]
// TODO: restriction placed by our syntype model, not required in Rust
#[rr::requires("layout_wf (Layout (Z.to_nat new_size) (Z.to_nat align_log2))")]
#[rr::requires(#type "ptr_old" : "v" @ "value_t (UntypedSynType (Layout (Z.to_nat old_size) (Z.to_nat align_log2)))")]
#[rr::requires(#iris "freeable_nz ptr_old (Z.to_nat old_size) 1 HeapAlloc")]
#[rr::exists("ptr_new", "v'")]
#[rr::returns("ptr_new")]
#[rr::ensures(#iris "freeable_nz ptr_new (Z.to_nat new_size) 1 HeapAlloc")]
#[rr::ensures(#type "ptr_new" : "v ++ v' : val" @ "value_t (UntypedSynType (Layout (Z.to_nat new_size) (Z.to_nat align_log2)))")]
#[rr::ensures("v' `has_layout_val` (Layout (Z.to_nat (new_size - old_size)) (Z.to_nat align_log2))")]
#[rr::ensures("min_alloc_start ≤ ptr_new.(loc_a) ≤ max_alloc_end")]
fn alloc_realloc_internal(old_size: usize, align_log2: usize, new_size: usize, ptr_old: *mut u8) -> *mut u8 {
    let new_ptr = alloc_alloc_internal(new_size, align_log2);
    // TODO implement cmp
    unsafe { copy_nonoverlapping(ptr_old, new_ptr, old_size.min(new_size)); }
    alloc_dealloc_internal(old_size, align_log2, ptr_old);
    new_ptr
}
