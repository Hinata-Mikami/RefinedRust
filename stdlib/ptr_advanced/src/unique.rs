
use core::ptr;
use crate::nonnull::NonNull;
use std::marker::PhantomData;
use core::mem;

// Note that, since RefinedRust does not feature an aliasing model, we do not enforce the aliasing
// contract of `Unique`.
#[rr::export_as(core::ptr::Unique)]
#[rr::refined_by("l" : "loc")]
pub struct Unique<T: ?Sized> {
    #[rr::field("l")]
    ptr: NonNull<T>,
    // NOTE: this marker has no consequences for variance, but is necessary
    // for dropck to understand that we logically own a `T`.
    //
    // For details, see:
    // https://github.com/rust-lang/rfcs/blob/master/text/0769-sound-generic-drop.md#phantom-data
    #[rr::field("tt")]
    _marker: PhantomData<T>,
}

#[rr::verify]
impl<T: ?Sized> Clone for Unique<T> {
    fn clone(&self) -> Self { *self }
}

#[rr::verify]
impl<T: ?Sized> Copy for Unique<T> {}

#[rr::export_as(core::ptr::Unique)]
impl<T: Sized> Unique<T> {
    #[rr::exists("l")]
    #[rr::returns("l")]
    #[rr::ensures("l `has_layout_loc` {ly_of T}")]
    #[rr::ensures(#type "l" : "()" @ "uninit UnitSynType")]
    #[rr::ensures(#iris "freeable_nz l 0 1 HeapAlloc")]
    pub const fn empty() -> Self {
        unsafe { Self::new_unchecked(ptr::dangling_mut()) }
    }
}

#[rr::export_as(core::ptr::Unique)]
impl<T: ?Sized> Unique<T> {
    #[rr::requires("ptr.(loc_a) ≠ 0")]
    #[rr::returns("ptr")]
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        unsafe {
            Unique { ptr: NonNull::new_unchecked(ptr), _marker: PhantomData }
        }
    }

    #[rr::returns("self")]
    pub const fn as_ptr(self) -> NonNull<T> { self.ptr }
}

//#[rr::verify]
//impl<T: ?Sized> From<NonNull<T>> for Unique<T> {
    //fn from(ptr: NonNull<T>) -> Self { Self { ptr, _marker: PhantomData } }
//}


