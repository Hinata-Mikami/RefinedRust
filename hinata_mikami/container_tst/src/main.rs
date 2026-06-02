#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]
#![allow(unused)]

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

// 成功していないが一旦skip
#[rr::trust_me]
#[rr::params("cell" : "loc", "next" : "loc", "v" : "Z", "old_next" : "loc")]
#[rr::args("cell", "next")]
#[rr::requires(#type "cell" : "(v, old_next)" @ "(Cell_inv_t <INST!>)")]
#[rr::ensures(#type "cell" : "(v, next)" @ "(Cell_inv_t <INST!>)")]
#[rr::returns("()")]
unsafe fn set_next(cell: *mut Cell, next: *mut Cell) {
    (*cell).next = next;
}


#[rr::refined_by("(xs, locs, nexts)" :
                 "(list Z * list (place_rfn loc) * list loc)")]
#[rr::depends_on(Cell)]
// #[rr::inv("Hnot_null": "Forall (λ l, l.(loc_a) ≠ 0) locs")]
#[rr::inv("Hnext_valid" : "Forall (λ n, n = NULL_loc ∨ #n ∈ locs) nexts")]
#[rr::inv(#iris "
  ([∗ list] i ↦ x ∈ xs,
    ∃ l n : loc,
      ⌜locs !! i = Some (#l)⌝ ∗
      ⌜nexts !! i = Some n⌝ ∗
      guarded true
        (l ◁ₗ[π, Owned]
          #(x, n)
          @ ◁(Cell_inv_t <INST!>)) ∗
      freeable_nz l
        (ly_size (use_layout_alg' Cell_sls))
        1 HeapAlloc)
")]
struct All_Cells {
    #[rr::field("locs")]
    all_cells: Vec<*mut Cell>,
}
// 任意長と固定長をかなり混同してしまった
// セル2個で，All_Cells {fst, scd} みたいな構造にしてもよかったかも

impl All_Cells {
    // ok
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

        All_Cells { all_cells }
    }


    // Type system got stuck in function "All_Cells_read_next_value"
    // https://chatgpt.com/s/t_6a1e5a38cc80819180ab9116c3b768d5
    // 手動証明を書くか，任意長Vecをあきらめるか？
    #[rr::params("a" : "loc", "b" : "loc", "v1" : "Z", "v2" : "Z", "γ")]
    #[rr::args("(([v1; v2], (<$#> [a; b]), [b; a]), γ)", "a")]
    #[rr::observe("γ": "([v1; v2], (<$#> [a; b]), [b; a])")]
    #[rr::returns("v2")]
    unsafe fn read_next_value(&mut self, cell: *mut Cell) -> i32 {
        let next = (*cell).next;
        (*next).value
    }
}

fn main() {
    let mut cells = All_Cells::new(10, 20);

    unsafe {
        let x = cells.read_next_value(cells.all_cells[0]);
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
a : loc
b : loc
v1 : Z
v2 : Z
γ : gname
arg_self : loc
arg_cell : loc
loop_map : BB_INV
tyvars : (TYVAR_MAP ∅)
H4 : CACHED
H5 : (MinInt usize ≤ loc_a a)
H6 : (loc_a a ≤ MaxInt usize)
H7 : CACHED
FN : function
R : typed_stmt_R_t
local___0 : loc
local_next : loc
---------------------------------------
_ : na_own π ⊤
_ : arg_self ◁ₗ[ π, Owned] # (# ([v1; v2], [# a; # b], [b; a]), γ) @
    (◁ &mut<ulft_1,∃; All_Cells_inv_t_inv_spec <INST!>,
                   (All_Cells_ty <INST!>)>)
_ : arg_cell ◁ₗ[ π, Owned] # a @ (◁ alias_ptr_t)
_ : "self" is_live{ (π, _fid), PtrSynType} arg_self
_ : "cell" is_live{ (π, _fid), PtrSynType} arg_cell
_ : credit_store 5 0
_ : "__0" is_live{ (π, _fid), IntSynType i32} local___0
_ : local___0 ◁ₗ[ π, Owned] .@ (◁ uninit (IntSynType i32))
_ : named_lfts
      (named_lft_update "plft3" ulft_1
         (named_lft_update "ulft_1" ulft_1
            (named_lft_update "_flft" ϝ (named_lft_update "static" static ∅))))
_ : allocated_locals (π, _fid) ["next"; "__0"; "self"; "cell"]
_ : "next" is_live{ (π, _fid), PtrSynType} local_next
_ : local_next ◁ₗ[ π, Owned] .@ (◁ uninit PtrSynType)
--------------------------------------∗
typed_val_expr [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_1] [ϝ ⊑ₗ{ 0} []] (
  π, _fid) (copy{PtrOp} (!{PtrOp}"cell" at{Cell_sls} "next"))%E
  (λ (L' : llctx) (v : val) (m : metadata) (rt : RT) (ty : type rt) (r : rt),
     [{ exhale ⌜m = MetaNone⌝;
        exhale True;
        {typed_write [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_1] L' (
           π, _fid) "next" PtrOp v ty r
           (λ L2 : llctx,
              introduce_with_hooks [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_1] L2
              [{ exhale ⧗ 2; {£ num_cred} }] HIDDEN_CONT)}
     }])

*/