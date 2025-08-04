#![rr::include("ptr")]
#![rr::include("result")]
#![rr::import("rrstd.alloc.theories", "layout")]
use std::ptr::Alignment;


#[rr::export_as(alloc::alloc::Layout)]
#[rr::refined_by("l" : "rust_layout")]
pub struct Layout {
    // size of the requested block of memory, measured in bytes.
    #[rr::field("Z.of_nat l.(layout_sz)")]
    size: usize,

    // alignment of the requested block of memory, measured in bytes.
    // we ensure that this is always a power-of-two, because API's
    // like `posix_memalign` require it and it is a reasonable
    // constraint to impose on Layout constructors.
    //
    // (However, we do not analogously require `align >= sizeof(void*)`,
    //  even though that is *also* a requirement of `posix_memalign`.)
    #[rr::field("l.(layout_alignment)")]
    align: Alignment,
}

#[rr::export_as(alloc::alloc::LayoutError)]
pub struct LayoutError;

#[rr::export_as(alloc::alloc::Layout)]
impl Layout {
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("Z.of_nat x.(layout_sz)")]
    pub const fn size(&self) -> usize {
        self.size
    }

    /*
    pub const fn from_size_align(size: usize, align: usize) -> Result<Self, LayoutError> {
        if Layout::is_size_align_valid(size, align) {
            // SAFETY: Layout::is_size_align_valid checks the preconditions for this call.
            unsafe { Ok(Layout { size, align: mem::transmute(align) }) }
        } else {
            Err(LayoutError)
        }
    }



    const fn is_size_align_valid(size: usize, align: usize) -> bool {
        let Some(align) = Alignment::new(align) else { return false };
        if size > Self::max_size_for_align(align) {
            return false;
        }
        true
    }

    const fn max_size_for_align(align: Alignment) -> usize {
        // (power-of-two implies align != 0.)
        // Rounded up size is:
        //   size_rounded_up = (size + align - 1) & !(align - 1);
        //
        // We know from above that align != 0. If adding (align - 1)
        // does not overflow, then rounding up will be fine.
        //

        // Conversely, &-masking with !(align - 1) will subtract off
        // only low-order-bits. Thus if overflow occurs with the sum,
        // the &-mask cannot subtract enough to undo that overflow.
        //
        // Above implies that checking for summation overflow is both
        // necessary and sufficient.

        // SAFETY: the maximum possible alignment is `isize::MAX + 1`,
        // so the subtraction cannot overflow.
        unsafe { unchecked_sub(isize::MAX as usize + 1, align.as_usize()) }
    }
    */
}
