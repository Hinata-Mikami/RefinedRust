#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.ptr")]
#![rr::import("stdlib.ptr.theories", "shims")]
#![rr::import("stdlib.ptr.theories", "specs")]
#![allow(unused)]

mod alignment;
use core::mem;


#[rr::export_as(core::ptr::write)]
#[rr::code_shim("ptr_write")]
#[rr::requires(#type "dst" : "()" @ "uninit {st_of T}")]
#[rr::ensures(#type "dst" : "$# src" @ "{ty_of T}")]
pub const fn write<T>(dst: *mut T, src:T) {
    unimplemented!();
}

#[rr::export_as(core::ptr::read)]
#[rr::code_shim("ptr_read")]
#[rr::params("r")]
#[rr::requires(#type "src" : "$# r" @ "{ty_of T}")]
#[rr::returns("r")]
#[rr::ensures(#type "src" : "()" @ "uninit {st_of T}")]
// TODO alternative spec that looses less information.
// However, some parts of the type system (e.g. enum initialization) cannot deal well yet with
// moving in values again.
//#[rr::params("vs")]
//#[rr::requires(#type "src" : "vs" @ "value_t {st_of T}")]
//#[rr::returns("vs" @ "value_t {st_of TA}")]
//#[rr::ensures(#type "src" : "vs" @ "value_t {st_of T}")]
pub const fn read<T>(src: *const T) -> T {
    unimplemented!();
}

#[rr::export_as(core::ptr::write_volatile)]
#[rr::requires(#type "dst" : "()" @ "uninit {st_of T}")]
#[rr::ensures(#type "dst" : "$# src" @ "{ty_of T}")]
pub const fn write_volatile<T>(dst: *mut T, src:T) {
    write(dst, src)
}

#[rr::export_as(core::ptr::read_volatile)]
#[rr::params("r")]
#[rr::requires(#type "src" : "$# r" @ "{ty_of T}")]
#[rr::returns("r")]
#[rr::ensures(#type "src" : "()" @ "uninit {st_of T}")]
pub const fn read_volatile<T>(src: *const T) -> T {
    read(src)
}



/* TODO: challenge for speccing this: what ownership do we require for src?
  - technically, we could require a shared ref.
    but: that is stronger than necessary - it asserts a validity invariant, whereas we should not require anything like that.
    is that also true if I have &shr (bytewise v) -- i.e. the type below the shared ref does not assert any validity invariant?
      I feel like that should be a pretty strong spec.
  - we could also try to take fractional ownership - but that would be quite a heavyweight change for this.
  - just take full ownership, similar to dst - but that is unnecessarily strong */
#[rr::export_as(core::ptr::copy_nonoverlapping)]
#[rr::code_shim("ptr_copy_nonoverlapping")]
#[rr::params("vs")]
#[rr::requires(#type "src" : "vs" @ "value_t (UntypedSynType (mk_array_layout {ly_of T} (Z.to_nat size)))")]
#[rr::requires(#type "dst" : "()" @ "uninit (UntypedSynType (mk_array_layout {ly_of T} (Z.to_nat size)))")]
#[rr::ensures(#type "src" : "vs" @ "value_t (UntypedSynType (mk_array_layout {ly_of T} (Z.to_nat size)))")]
#[rr::ensures(#type "dst" : "vs" @ "value_t (UntypedSynType (mk_array_layout {ly_of T} (Z.to_nat size)))")]
pub const fn copy_nonoverlapping<T>(
    src: *const T,
    dst: *mut T,
    size: usize,
) {
    let count: usize;
    unimplemented!();
}

// This spec really relies on the fact that the core type system does not usually disassemble arrays, but keeps them as one chunk in the context.
// (Of course, ptr::copy_nonoverlapping is an exception)
#[rr::export_as(core::ptr::copy)]
#[rr::only_spec]
#[rr::params("l", "off_src", "off_dst", "count", "len", "vs")]
#[rr::args("l offsetst{{ {st_of T} }}ₗ off_src", "l offsetst{{ {st_of T} }}ₗ off_dst", "count")]
#[rr::requires(#type "l" : "vs" @ "value_t (UntypedSynType (mk_array_layout {ly_of T} (Z.to_nat len)))")]
#[rr::requires("(0 ≤ count)%Z")]
#[rr::requires("0 ≤ off_src")]
#[rr::requires("0 ≤ off_dst")]
#[rr::requires("(off_src + count < len)%Z")]
#[rr::requires("(off_dst + count < len)%Z")]
#[rr::ensures(#type "l" : "ptr_copy_result off_src off_dst (Z.to_nat count) vs" @ "value_t (UntypedSynType (mk_array_layout {ly_of T} (Z.to_nat len)))")]
pub const fn copy<T>(src: *const T, dst: *mut T, count: usize) {
    unimplemented!();
}



#[rr::export_as(core::mem::size_of)]
#[rr::code_shim("mem_size_of")]
#[rr::returns("ly_size {ly_of T}")]
pub const fn mem_size_of<T>() -> usize {
    unimplemented!();
}

#[rr::export_as(core::mem::align_of)]
#[rr::code_shim("mem_align_of")]
#[rr::returns("ly_align {ly_of T}")]
pub const fn mem_align_of<T>() -> usize {
    unimplemented!();
}

#[rr::code_shim("mem_align_log_of")]
#[rr::returns("ly_align_log {ly_of T}")]
pub const fn mem_align_log_of<T>() -> usize {
    unimplemented!();
}

// TODO: offset, add, sub should require that the allocation is still alive, I think
#[rr::export_as(#method core::ptr::const_ptr::offset)]
#[rr::code_shim("ptr_offset")]
#[rr::requires("l `has_layout_loc` {ly_of T}")]
#[rr::requires("(count * size_of_st {st_of T})%Z ∈ isize_t")]
#[rr::requires(#iris "
    case_destruct (bool_decide (count < 0))%Z
      (λ b _, if b then loc_in_bounds l (Z.to_nat (-count) * size_of_st {st_of T}) 0 else loc_in_bounds l 0 (Z.to_nat count * size_of_st {st_of T}))")]
#[rr::returns("(l offsetst{{ {st_of T} }}ₗ count)")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn const_ptr_offset<T>(l: *const T, count: isize) -> *const T
{
    unimplemented!();
}

#[rr::export_as(#method core::ptr::mut_ptr::offset)]
#[rr::code_shim("ptr_offset")]
#[rr::requires("l `has_layout_loc` {ly_of T}")]
#[rr::requires("(count * size_of_st {st_of T})%Z ∈ isize_t")]
#[rr::requires(#iris "
    case_destruct (bool_decide (count < 0))%Z
      (λ b _, if b then loc_in_bounds l (Z.to_nat (-count) * size_of_st {st_of T}) 0 else loc_in_bounds l 0 (Z.to_nat count * size_of_st {st_of T}))")]
#[rr::returns("l offsetst{{ {st_of T} }}ₗ count")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn mut_ptr_offset<T>(l: *mut T, count: isize) -> *mut T
{
    unimplemented!();
}

#[rr::export_as(#method core::ptr::const_ptr::add)]
#[rr::requires("l `has_layout_loc` {ly_of T}")]
#[rr::requires("(count * size_of_st {st_of T})%Z ∈ isize_t")]
#[rr::requires(#iris "loc_in_bounds l 0 ((Z.to_nat count) * size_of_st {st_of T})")]
#[rr::returns("l offsetst{{ {st_of T} }}ₗ count")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn const_ptr_add<T>(l: *const T, count: usize) -> *const T {
    // NB: We can just truncate count to isize. 
    // - if T is a ZST, then the wrapped offset gets annihilated everywhere, so it's fine.
    // - else, we also know that it's in isize_t, so it's same as before.
    const_ptr_offset(l, count as isize)
}

#[rr::export_as(#method core::ptr::mut_ptr::add)]
#[rr::requires("l `has_layout_loc` {ly_of T}")]
#[rr::requires("(count * size_of_st {st_of T})%Z ∈ isize_t")]
#[rr::requires(#iris "loc_in_bounds l 0 ((Z.to_nat count) * size_of_st {st_of T})")]
#[rr::returns("l offsetst{{ {st_of T} }}ₗ count")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn mut_ptr_add<T>(l: *mut T, count: usize) -> *mut T {
    // NB: We can just truncate count to isize. 
    // - if T is a ZST, then the wrapped offset gets annihilated everywhere, so it's fine.
    // - else, we also know that it's in isize_t, so it's same as before.
    mut_ptr_offset(l, count as isize)
}


#[rr::export_as(#method core::ptr::const_ptr::sub)]
#[rr::code_shim("ptr_sub")]
#[rr::requires("l `has_layout_loc` {ly_of T}")]
#[rr::requires("(count * size_of_st {st_of T})%Z ∈ isize_t")]
#[rr::requires(#iris "loc_in_bounds l (Z.to_nat count * size_of_st {st_of T}) 0")]
#[rr::returns("l offsetst{{ {st_of T} }}ₗ (-count)")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn const_ptr_sub<T>(l: *const T, count: usize) -> *const T {
    unimplemented!();
}

#[rr::export_as(#method core::ptr::mut_ptr::sub)]
#[rr::code_shim("ptr_sub")]
#[rr::requires("l `has_layout_loc` {ly_of T}")]
#[rr::requires("(count * size_of_st {st_of T})%Z ∈ isize_t")]
#[rr::requires(#iris "loc_in_bounds l ((Z.to_nat count) * size_of_st {st_of T}) 0")]
#[rr::returns("l offsetst{{ {st_of T} }}ₗ (-count)")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn mut_ptr_sub<T>(l: *mut T, count: usize) -> *mut T {
    unimplemented!();
}


/// Wrapping operations
#[rr::export_as(#method core::ptr::const_ptr::wrapping_offset)]
#[rr::code_shim("ptr_wrapping_offset")]
#[rr::returns("l wrapping_offsetst{{ {st_of T} }}ₗ count")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn const_ptr_wrapping_offset<T>(l: *const T, count: isize) -> *const T {
    unimplemented!();
}
#[rr::export_as(#method core::ptr::mut_ptr::wrapping_offset)]
#[rr::code_shim("ptr_wrapping_offset")]
#[rr::returns("l wrapping_offsetst{{ {st_of T} }}ₗ count")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn mut_ptr_wrapping_offset<T>(l: *mut T, count: isize) -> *mut T {
    unimplemented!();
}


#[rr::export_as(#method core::ptr::const_ptr::wrapping_add)]
#[rr::code_shim("ptr_wrapping_add")]
#[rr::returns("l wrapping_offsetst{{ {st_of T} }}ₗ count")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn const_ptr_wrapping_add<T>(l: *const T, count: usize) -> *const T {
    unimplemented!();
}
#[rr::export_as(#method core::ptr::mut_ptr::wrapping_add)]
#[rr::code_shim("ptr_wrapping_add")]
#[rr::returns("l wrapping_offsetst{{ {st_of T} }}ₗ count")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn mut_ptr_wrapping_add<T>(l: *mut T, count: usize) -> *mut T {
    unimplemented!();
}

#[rr::export_as(#method core::ptr::const_ptr::wrapping_sub)]
#[rr::code_shim("ptr_wrapping_sub")]
#[rr::returns("l wrapping_offsetst{{ {st_of T} }}ₗ -count")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn const_ptr_wrapping_sub<T>(l: *const T, count: usize) -> *const T {
    unimplemented!();
}
#[rr::export_as(#method core::ptr::mut_ptr::wrapping_sub)]
#[rr::code_shim("ptr_wrapping_sub")]
#[rr::returns("l wrapping_offsetst{{ {st_of T} }}ₗ -count")]
#[rr::ensures(#iris "£ (S (num_laters_per_step 1)) ∗ atime 1")]
pub const fn mut_ptr_wrapping_sub<T>(l: *mut T, count: usize) -> *mut T {
    unimplemented!();
}

/// Casts
#[rr::export_as(#method core::ptr::const_ptr::cast)]
#[rr::returns("x")]
pub const fn const_ptr_cast<T, U>(x: *const T) -> *const U {
    x as _
}
#[rr::export_as(#method core::ptr::mut_ptr::cast)]
#[rr::returns("x")]
pub const fn mut_ptr_cast<T, U>(x: *mut T) -> *mut U {
    x as _
}

#[rr::export_as(#method core::ptr::mut_ptr::cast_const)]
#[rr::returns("x")]
pub const fn mut_ptr_cast_const<T>(x: *mut T) -> *const T {
    x as _
}
#[rr::export_as(#method core::ptr::const_ptr::cast_mut)]
#[rr::returns("x")]
pub const fn const_ptr_cast_mut<T>(x: *const T) -> *mut T {
    x as _
}



/// Strict provenance things


// TODO: addr, with_addr, map_addr

//#[rr::export_as(#method core::ptr::const_ptr::addr)]
//#[rr::code_shim()]
//#[rr::returns("x.2")]
//pub fn addr<T>(x: *const T) -> usize {
    //unimplemented!();
//}


// TODO: replaced in newer Rust versions by `without_provenance`
#[rr::export_as(core::ptr::invalid)]
#[rr::code_shim("ptr_invalid")]
#[rr::requires("(min_alloc_start ≤ addr)%Z")]
#[rr::requires("(addr ≤ max_alloc_end)%Z")]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures("l `aligned_to` (Z.to_nat addr)")]
#[rr::ensures("l.2 = addr")]
#[rr::ensures(#type "l" : "()" @ "unit_t")]
pub const fn invalid<T>(addr: usize) -> *const T {
    unimplemented!();
}
#[rr::export_as(core::ptr::invalid_mut)]
#[rr::code_shim("ptr_invalid")]
#[rr::requires("(min_alloc_start ≤ addr)%Z")]
#[rr::requires("(addr ≤ max_alloc_end)%Z")]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures("l `aligned_to` (Z.to_nat addr)")]
#[rr::ensures("l.2 = addr")]
#[rr::ensures(#type "l" : "()" @ "unit_t")]
pub const fn invalid_mut<T>(addr: usize) -> *mut T {
    unimplemented!();
}

#[rr::export_as(core::ptr::without_provenance)]
#[rr::code_shim("ptr_invalid")]
#[rr::requires("(min_alloc_start ≤ addr)%Z")]
#[rr::requires("(addr ≤ max_alloc_end)%Z")]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures("l `aligned_to` (Z.to_nat addr)")]
#[rr::ensures("l.2 = addr")]
#[rr::ensures(#type "l" : "()" @ "unit_t")]
pub const fn without_provenance<T>(addr: usize) -> *const T {
    unimplemented!();
}
#[rr::export_as(core::ptr::without_provenance_mut)]
#[rr::code_shim("ptr_invalid")]
#[rr::requires("(min_alloc_start ≤ addr)%Z")]
#[rr::requires("(addr ≤ max_alloc_end)%Z")]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures("l `aligned_to` (Z.to_nat addr)")]
#[rr::ensures("l.2 = addr")]
#[rr::ensures(#type "l" : "()" @ "unit_t")]
pub const fn without_provenance_mut<T>(addr: usize) -> *mut T {
    unimplemented!();
}

#[rr::export_as(core::ptr::dangling)]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures("l `has_layout_loc` {ly_of T}")]
#[rr::ensures(#type "l" : "()" @ "uninit UnitSynType")]
#[rr::ensures(#iris "freeable_nz l 0 1 HeapAlloc")]
pub const fn dangling<T>() -> *const T {
    without_provenance(mem_align_of::<T>())
}
#[rr::export_as(core::ptr::dangling_mut)]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures("l `has_layout_loc` {ly_of T}")]
#[rr::ensures(#type "l" : "()" @ "uninit UnitSynType")]
#[rr::ensures(#iris "freeable_nz l 0 1 HeapAlloc")]
pub const fn dangling_mut<T>() -> *mut T {
    without_provenance_mut(mem_align_of::<T>())
}
