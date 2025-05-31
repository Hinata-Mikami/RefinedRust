
#[rr::export_as(core::ptr::NonNull)]
#[repr(transparent)]
#[rr::refined_by("l" : "loc")]
#[rr::invariant("l.2 ≠ 0")]
pub struct NonNull<T: ?Sized> {
    // Remember to use `.as_ptr()` instead of `.pointer`, as field projecting to
    // this is banned by <https://github.com/rust-lang/compiler-team/issues/807>.
    #[rr::field("l")]
    pointer: *const T,
}

#[rr::export_as(core::ptr::NonNull)]
impl<T> NonNull<T> {

    /*
    #[rr::requires("(min_alloc_start ≤ addr)%Z")]
    #[rr::exists("l")]
    #[rr::returns("l")]
    #[rr::ensures("l `aligned_to` (Z.to_nat addr)")]
    #[rr::ensures("l.2 = addr")]
    #[rr::ensures(#type "l" : "()" @ "unit_t")]
    pub const fn without_provenance(addr: NonZero<usize>) -> Self {
        let pointer = crate::without_provenance(addr.get());

        // SAFETY: we know `addr` is non-zero.
        unsafe { NonNull { pointer } }
    }
    */
}
