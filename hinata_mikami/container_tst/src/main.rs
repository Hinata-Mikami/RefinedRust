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

// struct Cell
// struct All_Cells
// fn All_Cells::new(v1: i32, v2: i32) -> Self

// fn 
// fn set_next(cell: *mut Cell, next: *mut Cell)
// fn read_next_value_raw(cell: *mut Cell) -> i32


// #[rr::refined_by("(v, next)" : "(Z * loc)")]
struct Cell {
    // #[rr::field("v")]
    value: i32,

    // #[rr::field("next")]
    next: *mut Cell,
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
// そのため，r @ Cell_inv_t -> -[r] @ Cell_ty に変換
#[rr::inv(#iris "
  ([∗ list] i ↦ x ∈ xs,
    ∃ l n : loc,
      ⌜locs !! i = Some (#l)⌝ ∗
      ⌜nexts !! i = Some n⌝ ∗
      guarded true
        (l ◁ₗ[π, Owned]
          # -[#x; #n]
          @ ◁(Cell_ty <INST!>)) ∗
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

    // Cell_inv_t -> Cell_ty にしたことでエラーに
    // Box が返す所有権が Cell_inv_t -> 畳み込めない
    // 洗い出しのためBoxを使う部分をヘルパー関数(make_cells)に
    #[rr::params("v1" : "Z", "v2" : "Z")]
    #[rr::args("v1", "v2")]
    #[rr::requires("MinInt i32 ≤ v1")]
    #[rr::requires("v1 ≤ MaxInt i32")]
    #[rr::requires("MinInt i32 ≤ v2")]
    #[rr::requires("v2 ≤ MaxInt i32")]
    #[rr::exists("a" : "loc", "b" : "loc")]
    #[rr::returns("([v1; v2], (<$#> [a; b]), [b; a])")]
    #[rr::ensures("a.(loc_a) ≠ 0")]
    #[rr::ensures("b.(loc_a) ≠ 0")]
    fn new(v1: i32, v2: i32) -> Self {
        let a = make_cell(v1);
        let b = make_cell(v2);

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

    // head = a, a.next = b, b.value = v2
    // #[rr::params("a" : "loc", "b" : "loc", "v1" : "Z", "v2" : "Z", "γ")]
    // #[rr::args("(([v1; v2], (<$#> [a; b]), [b; a]), γ)")]
    // #[rr::observe("γ": "([v1; v2], (<$#> [a; b]), [b; a])")]
    // #[rr::returns("v2")]
    // unsafe fn read_next_value(&mut self) -> i32 {
    //     let cell = self.head;
    //     let next = unsafe { (*cell).next };
    //     let v = unsafe { (*next).value };
    //     v
    // }
}

// All_Cells::new 内のエラーの洗い出し
// ok
// struct Cellのrefined_byを削除したら通った

// 以下 ChatGPT より
// #[rr::refined_by(...)] により RefinedRust が Cell の外向きの型として Cell_inv_t を生成・使用。
// 消したことで、Cell_inv_t が不要に
// Box::new / Box::into_raw が Cell_ty 側の所有権を返すようになった
// または少なくとも Cell_inv_t を経由しなくなった。

// #[rr::trust_me]
#[rr::params("v" : "Z")]
#[rr::args("v")]
#[rr::requires("MinInt i32 ≤ v")]
#[rr::requires("v ≤ MaxInt i32")]
#[rr::exists("l" : "loc")]
#[rr::returns("l")]
#[rr::ensures(#type "l" : "-[#v; #NULL_loc]" @ "(Cell_ty <INST!>)")]
#[rr::ensures(#iris "freeable_nz l (ly_size (use_layout_alg' Cell_sls)) 1 HeapAlloc")]
#[rr::ensures("l.(loc_a) ≠ 0")]
#[rr::ensures("MinInt usize ≤ l.(loc_a)")]
#[rr::ensures("l.(loc_a) ≤ MaxInt usize")]
fn make_cell(v: i32) -> *mut Cell {
    let boxed = Box::new(Cell {
        value: v,
        next: std::ptr::null_mut(),
    });
    Box::into_raw(boxed)
}

// #[rr::trust_me]
// ok?
#[rr::params("cell" : "loc", "next" : "loc", "v" : "Z", "old_next" : "loc")]
#[rr::args("cell", "next")]
#[rr::requires(#type "cell" : "-[#v; #old_next]" @ "(Cell_ty <INST!>)")]
#[rr::ensures(#type "cell" : "-[#v; #next]" @ "(Cell_ty <INST!>)")]
#[rr::returns("()")]
unsafe fn set_next(cell: *mut Cell, next: *mut Cell) {
    unsafe {
        (*cell).next = next;
    }
}

// ok (All_Cells のメソッドとしてではなく，任意のセルからnextを読む方針)
#[rr::params(
    "cell" : "loc",
    "next" : "loc",
    "v" : "Z",
    "next_v" : "Z",
    "next_next" : "loc"
)]
#[rr::args("cell")]
#[rr::requires("next.(loc_a) ≠ 0")]
#[rr::requires(#type "cell" : "-[#v; #next]" @ "(Cell_ty <INST!>)")]
#[rr::requires(#type "next" : "-[#next_v; #next_next]" @ "(Cell_ty <INST!>)")]
#[rr::ensures(#type "cell" : "-[#v; #next]" @ "(Cell_ty <INST!>)")]
#[rr::ensures(#type "next" : "-[#next_v; #next_next]" @ "(Cell_ty <INST!>)")]
#[rr::returns("next_v")]
unsafe fn read_next_value_raw(cell: *mut Cell) -> i32 {
    let next = unsafe { (*cell).next };
    unsafe { (*next).value }
}


fn main() {
    let mut cells = All_Cells::new(10, 20);

    unsafe {
        let x = read_next_value_raw(cells.head);
        let _ = x;
    }
}

// セルへのrawポインタを受け取って，セルにアクセスするメソッド（最低限の例）
// 事前条件・事後条件をどう定義すればいいかをいろいろ試してみることから
