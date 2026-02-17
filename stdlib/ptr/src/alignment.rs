
#[rr::export_as(core::ptr::Alignment)]
#[rr::refined_by("x" : "alignment_enum")]
#[derive(Copy, Clone)]
pub struct Alignment(#[rr::field("x")] AlignmentEnum);

/// Radium works with a 64-bit pointer representation.
#[repr(u64)]
#[rr::refined_by("alignment_enum")]
#[derive(Copy, Clone)]
enum AlignmentEnum {
    #[rr::pattern("_Align1Shl0")]
    _Align1Shl0 = 1 << 0,
    #[rr::pattern("_Align1Shl1")]
    _Align1Shl1 = 1 << 1,
    #[rr::pattern("_Align1Shl2")]
    _Align1Shl2 = 1 << 2,
    #[rr::pattern("_Align1Shl3")]
    _Align1Shl3 = 1 << 3,
    #[rr::pattern("_Align1Shl4")]
    _Align1Shl4 = 1 << 4,
    #[rr::pattern("_Align1Shl5")]
    _Align1Shl5 = 1 << 5,
    #[rr::pattern("_Align1Shl6")]
    _Align1Shl6 = 1 << 6,
    #[rr::pattern("_Align1Shl7")]
    _Align1Shl7 = 1 << 7,
    #[rr::pattern("_Align1Shl8")]
    _Align1Shl8 = 1 << 8,
    #[rr::pattern("_Align1Shl9")]
    _Align1Shl9 = 1 << 9,
    #[rr::pattern("_Align1Shl10")]
    _Align1Shl10 = 1 << 10,
    #[rr::pattern("_Align1Shl11")]
    _Align1Shl11 = 1 << 11,
    #[rr::pattern("_Align1Shl12")]
    _Align1Shl12 = 1 << 12,
    #[rr::pattern("_Align1Shl13")]
    _Align1Shl13 = 1 << 13,
    #[rr::pattern("_Align1Shl14")]
    _Align1Shl14 = 1 << 14,
    #[rr::pattern("_Align1Shl15")]
    _Align1Shl15 = 1 << 15,
    #[rr::pattern("_Align1Shl16")]
    _Align1Shl16 = 1 << 16,
    #[rr::pattern("_Align1Shl17")]
    _Align1Shl17 = 1 << 17,
    #[rr::pattern("_Align1Shl18")]
    _Align1Shl18 = 1 << 18,
    #[rr::pattern("_Align1Shl19")]
    _Align1Shl19 = 1 << 19,
    #[rr::pattern("_Align1Shl20")]
    _Align1Shl20 = 1 << 20,
    #[rr::pattern("_Align1Shl21")]
    _Align1Shl21 = 1 << 21,
    #[rr::pattern("_Align1Shl22")]
    _Align1Shl22 = 1 << 22,
    #[rr::pattern("_Align1Shl23")]
    _Align1Shl23 = 1 << 23,
    #[rr::pattern("_Align1Shl24")]
    _Align1Shl24 = 1 << 24,
    #[rr::pattern("_Align1Shl25")]
    _Align1Shl25 = 1 << 25,
    #[rr::pattern("_Align1Shl26")]
    _Align1Shl26 = 1 << 26,
    #[rr::pattern("_Align1Shl27")]
    _Align1Shl27 = 1 << 27,
    #[rr::pattern("_Align1Shl28")]
    _Align1Shl28 = 1 << 28,
    #[rr::pattern("_Align1Shl29")]
    _Align1Shl29 = 1 << 29,
    #[rr::pattern("_Align1Shl30")]
    _Align1Shl30 = 1 << 30,
    #[rr::pattern("_Align1Shl31")]
    _Align1Shl31 = 1 << 31,
    #[rr::pattern("_Align1Shl32")]
    _Align1Shl32 = 1 << 32,
    #[rr::pattern("_Align1Shl33")]
    _Align1Shl33 = 1 << 33,
    #[rr::pattern("_Align1Shl34")]
    _Align1Shl34 = 1 << 34,
    #[rr::pattern("_Align1Shl35")]
    _Align1Shl35 = 1 << 35,
    #[rr::pattern("_Align1Shl36")]
    _Align1Shl36 = 1 << 36,
    #[rr::pattern("_Align1Shl37")]
    _Align1Shl37 = 1 << 37,
    #[rr::pattern("_Align1Shl38")]
    _Align1Shl38 = 1 << 38,
    #[rr::pattern("_Align1Shl39")]
    _Align1Shl39 = 1 << 39,
    #[rr::pattern("_Align1Shl40")]
    _Align1Shl40 = 1 << 40,
    #[rr::pattern("_Align1Shl41")]
    _Align1Shl41 = 1 << 41,
    #[rr::pattern("_Align1Shl42")]
    _Align1Shl42 = 1 << 42,
    #[rr::pattern("_Align1Shl43")]
    _Align1Shl43 = 1 << 43,
    #[rr::pattern("_Align1Shl44")]
    _Align1Shl44 = 1 << 44,
    #[rr::pattern("_Align1Shl45")]
    _Align1Shl45 = 1 << 45,
    #[rr::pattern("_Align1Shl46")]
    _Align1Shl46 = 1 << 46,
    #[rr::pattern("_Align1Shl47")]
    _Align1Shl47 = 1 << 47,
    #[rr::pattern("_Align1Shl48")]
    _Align1Shl48 = 1 << 48,
    #[rr::pattern("_Align1Shl49")]
    _Align1Shl49 = 1 << 49,
    #[rr::pattern("_Align1Shl50")]
    _Align1Shl50 = 1 << 50,
    #[rr::pattern("_Align1Shl51")]
    _Align1Shl51 = 1 << 51,
    #[rr::pattern("_Align1Shl52")]
    _Align1Shl52 = 1 << 52,
    #[rr::pattern("_Align1Shl53")]
    _Align1Shl53 = 1 << 53,
    #[rr::pattern("_Align1Shl54")]
    _Align1Shl54 = 1 << 54,
    #[rr::pattern("_Align1Shl55")]
    _Align1Shl55 = 1 << 55,
    #[rr::pattern("_Align1Shl56")]
    _Align1Shl56 = 1 << 56,
    #[rr::pattern("_Align1Shl57")]
    _Align1Shl57 = 1 << 57,
    #[rr::pattern("_Align1Shl58")]
    _Align1Shl58 = 1 << 58,
    #[rr::pattern("_Align1Shl59")]
    _Align1Shl59 = 1 << 59,
    #[rr::pattern("_Align1Shl60")]
    _Align1Shl60 = 1 << 60,
    #[rr::pattern("_Align1Shl61")]
    _Align1Shl61 = 1 << 61,
    #[rr::pattern("_Align1Shl62")]
    _Align1Shl62 = 1 << 62,
    #[rr::pattern("_Align1Shl63")]
    _Align1Shl63 = 1 << 63,
}

#[rr::export_as(core::ptr::Alignment)]
impl Alignment {

    #[rr::only_spec]
    #[rr::requires("is_power_of_two (Z.to_nat align)")]
    #[rr::returns("alignment_of_align align")]
    pub const unsafe fn new_unchecked(align: usize) -> Self {
        unimplemented!();
        // SAFETY: By precondition, this must be a power of two, and
        // our variants encompass all possible powers of two.
        //unsafe { mem::transmute::<usize, Alignment>(align) }
    }

    #[rr::ok]
    #[rr::requires("is_power_of_two (Z.to_nat align)")]
    #[rr::ensures("ret = alignment_of_align align")]
    pub const fn new(align: usize) -> Option<Self> {
        if align.is_power_of_two() {
            // SAFETY: Just checked it only has one bit set
            Some(unsafe { Self::new_unchecked(align) })
        } else {
            None
        }
    }

    #[rr::returns("alignment_of_align (ly_align {ly_of T})")]
    pub const fn of<T>() -> Self {
        // This can't actually panic since type alignment is always a power of two.
        Alignment::new(align_of::<T>()).unwrap()
    }

    #[rr::returns("alignment_to_align self")]
    pub const fn as_usize(self) -> usize {
        self.0 as usize
    }
}
