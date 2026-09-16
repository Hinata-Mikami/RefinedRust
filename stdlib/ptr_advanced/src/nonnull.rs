
use core::ptr;


#[rr::export_as(core::ptr::NonNull)]
#[repr(transparent)]
#[rr::refined_by("l" : "loc")]
#[rr::invariant("l.(loc_a) ≠ 0")]
pub struct NonNull<T: ?Sized> {
    // Remember to use `.as_ptr()` instead of `.pointer`, as field projecting to
    // this is banned by <https://github.com/rust-lang/compiler-team/issues/807>.
    #[rr::field("#(l)")]
    pointer: *const T,
}

#[rr::verify]
impl<T: ?Sized> Clone for NonNull<T> {
    fn clone(&self) -> Self { *self }
}

#[rr::verify]
impl<T: ?Sized> Copy for NonNull<T> {}


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

#[rr::export_as(core::ptr::NonNull)]
impl<T: ?Sized> NonNull<T> {
    #[rr::requires("ptr.(loc_a) ≠ 0")]
    #[rr::returns("ptr")]
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        // SAFETY: the caller must guarantee that `ptr` is non-null.
        unsafe {
            NonNull { pointer: ptr as _ }
        }
    }
    
    #[rr::returns("if decide (ptr.(loc_a) = 0) then None else Some ptr")]
    pub const fn new(ptr: *mut T) -> Option<Self> {
        if !ptr.is_null() {
            // SAFETY: The pointer is already checked and is not null
            Some(unsafe { Self::new_unchecked(ptr) })
        } else {
            None
        }
    }

    #[rr::returns("self")]
    pub const fn as_ptr(self) -> *mut T {
        // stdlib is doing a transmute, but that is hard.
        self.pointer as *mut T
    }

    #[rr::params("x" : "{xt_of T}")]
    #[rr::requires(#iris "self ◁ₗ[π, Owned] # ($# x) @ ◁ {ty_of T}")]
    #[rr::ensures(#iris "self ◁ₗ[π, Owned] # ($# x) @ ShrBlockedLtype {ty_of T} {'a}")]
    #[rr::returns("x")]
    pub const unsafe fn as_ref<'a>(&self) -> &'a T {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        // `cast_const` avoids a mutable raw pointer deref.
        unsafe { &*self.as_ptr().cast_const() }
    }

    #[rr::params("x" : "{xt_of T}")]
    #[rr::requires(#iris "self.cur ◁ₗ[π, Owned] # ($# x) @ ◁ {ty_of T}")]
    #[rr::exists("γ")]
    #[rr::ensures(#iris "self.cur ◁ₗ[π, Owned] PlaceGhost γ @ BlockedLtype {ty_of T} {'a}")]
    #[rr::observe("self.ghost" : "self.cur")] 
    #[rr::returns("(x, γ)")]
    pub const unsafe fn as_mut<'a>(&mut self) -> &'a mut T {
        unsafe {
            &mut *self.as_ptr()
        }
    }

    #[rr::returns("self")]
    pub const fn cast<U>(self) -> NonNull<U> {
        // SAFETY: `self` is a `NonNull` pointer which is necessarily non-null
        unsafe { NonNull { pointer: self.as_ptr() as *mut U } }
    }

    // This spec only works for Copyable type, as it is hard to state what happens for `Shared`
    // ownership otherwise.
    // If you actually own the underlying memory, move out the value ownership before (`value_t` is
    // Copy).
    #[rr::params("k", "ty" : "xtype")]
    #[rr::unsafe_elctx("bor_kind_outlives_elctx k ϝ")]
    #[rr::requires(#iris "self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty)")]
    #[rr::requires("ty_allows_reads ty.(xtype_ty)")]
    #[rr::requires("ty_allows_writes ty.(xtype_ty)")]
    // (`read` does a typed Copy at the syntype of T)
    #[rr::requires("st_of ty.(xtype_ty) MetaNone = {st_of T}")]
    #[rr::requires("Copyable ty.(xtype_ty)")]
    #[rr::ensures(#iris "self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty)")]
    #[rr::returns("ty.(xtype_rfn)" @ "ty.(xtype_ty)")]
    pub const unsafe fn read(self) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `read`.
        unsafe { ptr::read(self.as_ptr()) }
    }

    #[rr::params("k", "ty" : "xtype")]
    #[rr::unsafe_elctx("bor_kind_outlives_elctx k ϝ")]
    #[rr::requires(#iris "self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty)")]
    #[rr::requires("ty_allows_reads ty.(xtype_ty)")]
    #[rr::requires("ty_allows_writes ty.(xtype_ty)")]
    #[rr::requires("st_of ty.(xtype_ty) MetaNone = {st_of T}")]
    #[rr::requires("Copyable ty.(xtype_ty)")]
    #[rr::ensures(#iris "self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty)")]
    #[rr::returns("ty.(xtype_rfn)" @ "ty.(xtype_ty)")]
    pub unsafe fn read_volatile(self) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `read_volatile`.
        unsafe { ptr::read_volatile(self.as_ptr()) }
    }

    #[rr::requires(#type "self" : "()" @ "uninit {st_of T}")]
    #[rr::ensures(#type "self" : "$# val" @ "{ty_of T}")]
    pub const unsafe fn write(self, val: T)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write`.
        unsafe { ptr::write(self.as_ptr(), val) }
    }

    #[rr::requires(#type "self" : "()" @ "uninit {st_of T}")]
    #[rr::ensures(#type "self" : "$# val" @ "{ty_of T}")]
    pub unsafe fn write_volatile(self, val: T)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write_volatile`.
        unsafe { ptr::write_volatile(self.as_ptr(), val) }
    }

    #[rr::returns("bool_decide (self `aligned_to` (ly_align {ly_of T}))")]
    pub fn is_aligned(self) -> bool
    where
        T: Sized,
    {
        self.as_ptr().is_aligned()
    }

    #[rr::requires("is_power_of_two (Z.to_nat align)")]
    #[rr::returns("bool_decide (self `aligned_to` Z.to_nat align)")]
    pub fn is_aligned_to(self, align: usize) -> bool {
        self.as_ptr().is_aligned_to(align)
    }

}
