#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]
#![allow(unused)]
#![allow(non_camel_case_types)]

#![rr::include("stdlib")]
#![rr::include("vec")]
#![rr::include("option")]
#![rr::include("ptr")]
#![rr::include("mem")]
#![rr::include("rr_internal")]

use std::ptr;

#[rr::refined_by("(v, next)" : "(Z * loc)")]
struct Cell {
    #[rr::field("v")]
    value: i32,

    #[rr::field("next")]
    next: *mut Cell,
}

// まだ一旦 trust_me
#[rr::trust_me]
#[rr::params("cell" : "loc", "next" : "loc", "v" : "Z", "old_next" : "loc")]
#[rr::args("cell", "next")]
#[rr::requires(#type "cell" : "(v, old_next)" @ "(Cell_inv_t <INST!>)")]
#[rr::ensures(#type "cell" : "(v, next)" @ "(Cell_inv_t <INST!>)")]
#[rr::returns("()")]
unsafe fn set_next(cell: *mut Cell, next: *mut Cell) {
    unsafe {
        (*cell).next = next;
    }
}


#[rr::refined_by("(xs, locs, nexts)" :
                 "(list Z * list (place_rfn loc) * list loc)")]
#[rr::exists("hd" : "loc")]
#[rr::depends_on(Cell)]
#[rr::inv("Hhead" : "locs !! 0%nat = Some (#hd)")]
#[rr::inv("Hlen_locs" : "length locs = length xs")]
#[rr::inv("Hlen_nexts" : "length nexts = length xs")]
#[rr::inv("Hnext_valid" : "Forall (λ n, n = NULL_loc ∨ #n ∈ locs) nexts")]
// StructLtype を Cell_inv_t に自動で畳み込めない
// #[rr::inv(#iris "
//   ([∗ list] i ↦ x ∈ xs,
//     ∃ l n : loc,
//       ⌜locs !! i = Some (#l)⌝ ∗
//       ⌜nexts !! i = Some n⌝ ∗
//       guarded true
//         (l ◁ₗ[π, Owned]
//           #(x, n)
//           @ ◁(Cell_inv_t <INST!>)) ∗
//       freeable_nz l
//         (ly_size (use_layout_alg' Cell_sls))
//         1 HeapAlloc)
// ")]

shareable_ltype_own の instance @ ◁ ty の形 にマッチしない
#[rr::inv(#iris "
  ([∗ list] i ↦ x ∈ xs,
    ∃ l n : loc,
      ⌜locs !! i = Some (#l)⌝ ∗
      ⌜nexts !! i = Some n⌝ ∗
      guarded true
        (l ◁ₗ[π, Owned]
          # -[#x; #n]
          @ StructLtype +[◁ int i32; ◁ alias_ptr_t] Cell_sls) ∗
      freeable_nz l
        (ly_size (use_layout_alg' Cell_sls))
        1 HeapAlloc)
")]

struct All_Cells {
    #[rr::field("locs")]
    all_cells: Vec<*mut Cell>,

    #[rr::field("hd")]
    head: *mut Cell,
}

impl All_Cells {
    #[rr::params("v1" : "Z", "v2" : "Z")]
    #[rr::args("v1", "v2")]
    #[rr::requires("MinInt i32 ≤ v1")]
    #[rr::requires("v1 ≤ MaxInt i32")]
    #[rr::requires("MinInt i32 ≤ v2")]
    #[rr::requires("v2 ≤ MaxInt i32")]
    #[rr::exists("a" : "loc", "b" : "loc")]
    #[rr::returns("([v1; v2], (<$#> [a; b]), [b; a])")]
    fn new(v1: i32, v2: i32) -> Self {
        let boxed_a = Box::new(Cell {
            value: v1,
            next: std::ptr::null_mut(),
        });
        let a = Box::into_raw(boxed_a);

        let boxed_b = Box::new(Cell {
            value: v2,
            next: std::ptr::null_mut(),
        });
        let b = Box::into_raw(boxed_b);

        unsafe {
            set_next(a, b);
            set_next(b, a);
        }

        let mut all_cells = Vec::new();
        all_cells.push(a);
        all_cells.push(b);

        All_Cells {
            all_cells,
            head: a,
        }
    }

    // Vec indexing 不可 -> とりあえず all_cells に head を作る
    // head = a, a.next = b, b.value = v2
    #[rr::params("a" : "loc", "b" : "loc", "v1" : "Z", "v2" : "Z", "γ")]
    #[rr::args("(([v1; v2], (<$#> [a; b]), [b; a]), γ)")]
    #[rr::observe("γ": "([v1; v2], (<$#> [a; b]), [b; a])")]
    #[rr::returns("v2")]
    unsafe fn read_next_value(&mut self) -> i32 {
        let cell = self.head;
        let next = unsafe { (*cell).next };
        let v = unsafe { (*next).value };
        v
    }
}

fn main() {
    let mut cells = All_Cells::new(10, 20);

    unsafe {
        let x = cells.read_next_value();
        let _ = x;
    }
}

/*
Type system got stuck in function "All_Cells_read_next_value" !
Goal:
RRGS : (refinedrustGS Σ)
π : thread_id
FN_NAME : string
Cell_sl : struct_layout
H : CACHED
All_Cells_sl : struct_layout
H0 : CACHED
Hcache : JCACHED
Vec_sl : struct_layout
H1 : CACHED
Global_sl : struct_layout
core_marker_PhantomData_sl : struct_layout
H2 : CACHED
H3 : CACHED
ulft_1 : (id lft)
ϝ : lft
_fid : nat
v1 : Z
v2 : Z
γ : gname
arg_self : loc
loop_map : BB_INV
tyvars : (TYVAR_MAP ∅)
H4 : CACHED
FN : function
x0 : loc
x1 : loc
R : typed_stmt_R_t
l' : loc
local___0 : loc
x : thread_id
H6 : CACHED
Hnext_valid : (x0 = NULL_loc ∨ x0 = x1 ∨ True)
H5 : (x1 = NULL_loc ∨ True ∨ x1 = x0)
x2 : thread_id
H7 : CACHED
v : val
v0 : val
v3 : val
v4 : val
---------------------------------------
_ : na_own π ⊤
_ : named_lfts
      (named_lft_update "plft3" ulft_1
         (named_lft_update "ulft_1" ulft_1
            (named_lft_update "_flft" ϝ (named_lft_update "static" static ∅))))
_ : "self" is_live{ (π, _fid), PtrSynType} arg_self
_ : freeable_nz x1 (ly_size (use_layout_alg' Cell_sls)) 1 HeapAlloc
_ : freeable_nz x0 (ly_size (use_layout_alg' Cell_sls)) 1 HeapAlloc
_ : arg_self ◁ₗ[ π, Owned] # (# -[# [# x1; # x0]; # x1], γ) @
    MutLtype
      (OpenedLtype
         (StructLtype
            +[◁ (Vec_inv_t loc Global_rt GlobalasAllocator_spec_attrs <TY>
                 alias_ptr_t <TY> (Global_ty <INST!>) <INST!>); ◁ alias_ptr_t]
            All_Cells_sls)
         (◁ (All_Cells_ty <INST!>))
         (◁ (∃; All_Cells_inv_t_inv_spec <INST!>, (All_Cells_ty <INST!>)))
         (λ (r : plist (RT_rt ∘ place_rfnRT)
                   [Vec_inv_t_rt loc Global_rt; loc]) '(
            xs, locs, nexts),
            ∃ hd : name_hint_ty "hd" loc, ⌜r = -[# locs; # hd]⌝ ∗
              ⌜name_hint "Hhead" (locs !! 0%nat = Some # hd)⌝ ∗
              ⌜name_hint "Hlen_locs" (length locs = length xs)⌝ ∗
              ⌜name_hint "Hlen_nexts" (length nexts = length xs)⌝ ∗
              ⌜name_hint "Hnext_valid"
                 (Forall (λ n : loc, n = NULL_loc ∨ # n ∈ locs) nexts)⌝ ∗
              ([∗ list] i↦x0 ∈ xs, ∃ l n : loc, ⌜locs !! i = Some # l⌝ ∗
                                     ⌜nexts !! i = Some n⌝ ∗
                                     guarded true
                                       (l ◁ₗ[ π, Owned] # (
                                        x0, n) @ (◁ (Cell_inv_t <INST!>))) ∗        // invariant で Cell_inv_t <INST!> 型を要求
                                     freeable_nz l
                                       (ly_size (use_layout_alg' Cell_sls)) 1
                                       HeapAlloc) ∗
              True)
         (λ (_ : plist (RT_rt ∘ place_rfnRT)
                   [Vec_inv_t_rt loc Global_rt; loc]) 
            (_ : list Z * list (place_rfn loc) * list loc), 
            llft_elt_toks [ϝ]))
      ulft_1
_ : x1 ◁ₗ[ π, Owned] # -[# v1; # x0] @                                  // たぶん cell
    StructLtype +[◁ int i32; ◁ alias_ptr_t] Cell_sls                    // Cell_inv_t <INST!> に畳み込めていないことが原因？
_ : x0 ◁ₗ[ π, Owned] # -[# v2; # x1] @                                  // たぶん next
    StructLtype +[◁ int i32; ◁ alias_ptr_t] Cell_sls
_ : "__0" is_live{ (π, _fid), IntSynType i32} local___0
_ : local___0 ◁ₗ[ π, Owned] # v2 @ (◁ int i32)                          // 返り値用ローカル? v2 は読めてる
_ : credit_store 45 18
_ : allocated_locals (π, _fid) ["__0"; "self"]
--------------------------------------∗
typed_val_expr [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_1] [ϝ ⊑ₗ{ 1} []] (
  π, _fid) (move{IntOp i32} "__0")%E
  (λ (L' : llctx) (v : val) (m : metadata) (rt : RT) (ty : type rt) (r :rt),
     introduce_with_hooks [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_1] L' 
     v ◁ᵥ{ π, m} r @ ty HIDDEN_CONT)
*/