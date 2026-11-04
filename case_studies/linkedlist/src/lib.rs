#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(dead_code)]
#![allow(unused)]

#![rr::package("linkedlist")]
#![rr::import("refinedrust.extra_proofs.linkedlist", "linkedlist")]
#![rr::include("stdlib")]
#![rr::include("mem")]
#![rr::include("sized")]

use std::marker::PhantomData;

mod examples;
mod demo;

#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind}")]
struct Link<T> {
    value: T,
    next: *const Link<T>,
    prev: *const Link<T>,
}

#[rr::refined_by("xs" : "listRT {rt_of T}")]
#[rr::depends_on(Link)]
#[rr::exists("locs" : "list loc", "hd_ptr" : "loc", "tl_ptr" : "loc")]
#[rr::inv("Hlocs" : "if decide (tl_ptr.(loc_a) = 0)
    then xs = [] ∧ hd_ptr = NULL_loc ∧ tl_ptr = NULL_loc
    else length xs > 0 ∧ head locs = Some hd_ptr ∧ last locs = Some tl_ptr")]
#[rr::inv("Hlen_eq": "length locs = length xs")]
#[rr::inv("hd_ptr.(loc_a) = 0 ↔ tl_ptr.(loc_a) = 0")]
// Needed to ensure we can turn ownership into a Box again for deallocation.
#[rr::inv("Hnot_null": "Forall (λ l, l.(loc_a) ≠ 0) locs")]
// Ownership of the Link pointer for every element.
#[rr::inv(#iris "([∗ list] i ↦ x ∈ xs,
    linkedlist_node π {T} (Link_sls {st_of T}) locs i x
    )")]
#[rr::ghost_drop(#iris "[∗ list] x ∈ xs, ty_ghost_drop {T} π x")]
#[rr::ty_lfts("ty_lfts {T}")]
#[rr::ty_wf_E("ty_wf_E {T}")]
#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind}")]
pub struct List<T> {
    #[rr::field("#(hd_ptr)")]
    first: *const Link<T>,
    #[rr::field("#(tl_ptr)")]
    last: *const Link<T>,
}

impl<T> List<T> {
    #[rr::returns("[]")]
    pub fn new() -> List<T> {
        List { first: std::ptr::null(), last: std::ptr::null() }
    }

    #[rr::observe("self.ghost": "<$#> (self.cur ++ [value])")]
    pub fn push_back(&mut self, value: T) {
        let link = Box::new(Link { value, next: std::ptr::null(), prev: self.last });
        let link_ptr = Box::into_raw(link);

        if self.last.is_null() {
            self.first = link_ptr;
            self.last = link_ptr;
        } else {
            let link_last = self.last as *mut Link<T>;
            unsafe { (*link_last).next = link_ptr; }
            self.last = link_ptr;
        }
    }

    #[rr::observe("self.ghost": "<$#> (value :: self.cur)")]
    pub fn push_front(&mut self, value: T) {
        let link = Box::new(Link { value, next: self.first, prev: std::ptr::null() });
        let link_ptr = Box::into_raw(link);

        if self.first.is_null() {
            self.last = link_ptr;
        } else {
            let old_first = self.first as *mut Link<T>;
            unsafe { (*old_first).prev = link_ptr; }
        }
        self.first = link_ptr;
    }

    #[rr::returns("head self.cur")]
    #[rr::observe("self.ghost": "<$#> (tail self.cur)")]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.first.is_null() {
            return None;
        }
        let link = self.first as *mut Link<T>;
        // directly deref the Box and move out of it, dropping the box.
        let link = *unsafe { Box::from_raw(link) };

        self.first = link.next;
        if self.first.is_null() {
            self.last = std::ptr::null_mut();
        } else {
            let new_first = self.first as *mut Link<T>;
            unsafe { (*new_first).prev = std::ptr::null(); }
        }
        Some(link.value)
    }

    #[rr::returns("last self.cur")]
    #[rr::observe("self.ghost": "<$#> (removelast self.cur)")]
    pub fn pop_back(&mut self) -> Option<T> {
        if self.last.is_null() {
            return None;
        }
        let link = self.last as *mut Link<T>;
        let link = *unsafe { Box::from_raw(link) };

        self.last = link.prev;
        if self.last.is_null() {
            self.first = std::ptr::null_mut();
        } else {
            let new_last = self.last as *mut Link<T>;
            unsafe { (*new_last).next = std::ptr::null(); }
        }
        Some(link.value)
    }

    #[rr::returns("head self.cur")]
    #[rr::observe("self.ghost": "<$#> (tail self.cur)")]
    pub fn pop_front_leaky(&mut self) -> Option<T> {
        if self.first.is_null() {
            return None;
        }
        let link = self.first as *mut Link<T>;

        let val = unsafe {
            self.first = (*link).next;
            (&raw mut (*link).value).read()
        };
        if self.first.is_null() {
            self.last = std::ptr::null_mut();
        } else {
            let new_first = self.first as *mut Link<T>;
            unsafe { (*new_first).prev = std::ptr::null(); }
        }
        // TODO free memory via alloc API.
        Some(val)
    }

    #[rr::returns("self")]
    pub fn iter(&self) -> ListIter<'_, T> {
        ListIter {
            current_link: self.first,
            phantom: PhantomData,
        }
    }
}

impl<T> Drop for List<T> {

    // Add a lifetime wellformedness constraint for &'a self;
    // this is not added automatically via RefinedRust's usual mechanism as 
    // we override the semantic type.
    #[rr::unsafe_elctx("ty_outlives_E {T} ulft_1")]
    #[rr::params("l", "xs")]
    #[rr::args("l" @ "alias_ref_t")]
    #[rr::requires(#type "l" : "$# xs" @ "List_inv_t T_rt -[] -[T_ty]")]
    #[rr::ensures(#iris "[∗ list] x ∈ xs, ty_ghost_drop {T} π ($# x)")]
    #[rr::ensures(#type "l" : "$# []" @ "List_inv_t T_rt -[] -[T_ty]")]
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
    #[rr::ensures_on_unwind(#iris "∃ remaining, l ◁ₗ[π, Owned] #($# remaining) @ (◁ List_inv_t T_rt -[] -[T_ty])")]
    fn drop(&mut self) {
        while let Some(value) = self.pop_front() {
            let _ =
            #[rr::exists("dropped", "remaining")]
            #[rr::inv(#type "l" : "$# remaining" @ "List_inv_t T_rt -[] -[T_ty]")]
            #[rr::inv(#iris "[∗ list] x ∈ dropped, ty_ghost_drop {T} π ($# x)")]
            #[rr::inv("xs = dropped ++ remaining")]
            #[rr::ignore] || {};

            std::mem::drop(value);
        }
    }
}


#[rr::refined_by("xs" : "listRT (directRT {xt_of T})")]
#[rr::depends_on(Link)]
#[rr::exists("locs" : "list loc", "hd_ptr" : "loc", "prev_ptr" : "loc")]
#[rr::inv("Hlocs" : "if decide (hd_ptr.(loc_a) = 0)
    then xs = [] ∧ hd_ptr = NULL_loc
    else length xs > 0 ∧ head locs = Some hd_ptr")]
#[rr::inv("Hlen_eq": "length locs = length xs")]
#[rr::inv("Hnot_null": "Forall (λ l, l.(loc_a) ≠ 0) locs")]
// Ownership of the Link pointer for every element.
#[rr::inv(#iris "([∗ list] i ↦ x ∈ xs,
    linkedlist_node_shared π {'a} {T} (Link_sls {st_of T}) locs prev_ptr i ($# x)
    )")]
#[rr::ty_lfts("ty_lfts {T}")]
#[rr::ty_wf_E("ty_wf_E {T}")]
#[derive(Copy, Clone)]
pub struct ListIter<'a, T> {
    #[rr::field("#(hd_ptr)")]
    current_link: *const Link<T>,
    #[rr::field("#(tt)")]
    phantom: PhantomData<&'a T>,
}

#[rr::instantiate("Params" := "unit")]
#[rr::instantiate("Inv" := "λ π _ s, True%I")]
#[rr::instantiate("Next" := "λ π _ l e l2,
    (⌜if_None e (l = [] ∧ l2 = [])⌝∗
    ⌜if_Some e (λ e, l = e :: l2)⌝)%I")]
impl<'a, T: 'a> Iterator for ListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_link.is_null() {
            None
        } else {
            let elem_ref = unsafe {
                &(*self.current_link).value
            };
            self.current_link = unsafe {
                (*self.current_link).next
            };
            Some(elem_ref)
        }
    }
}

#[rr::instantiate("IntoIter" := "λ x, x")]
impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = ListIter<'a, T>;

    #[rr::default_spec]
    fn into_iter(self: &'a List<T>) -> Self::IntoIter {
        self.iter()
    }
}
