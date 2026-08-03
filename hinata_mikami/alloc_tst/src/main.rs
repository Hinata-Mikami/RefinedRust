#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]
#![allow(unused)]
#![allow(non_camel_case_types)]
#![allow(unsafe_op_in_unsafe_fn)]

#![rr::include("stdlib")]
#![rr::include("vec")]
#![rr::include("option")]
#![rr::include("ptr")]
#![rr::include("mem")]
#![rr::include("rr_internal")]


struct Node {
    value: i32,
}

#[rr::params("v" : "Z")]
#[rr::args("v")]
#[rr::requires("MinInt i32 ≤ v")]
#[rr::requires("v ≤ MaxInt i32")]
#[rr::exists("ptr" : "loc")]
#[rr::returns("ptr")]
#[rr::ensures("ptr.(loc_a) ≠ 0")]
#[rr::ensures(#type "ptr" :
    "-[#v]" @ "(Node_ty <INST!>)"
)]
#[rr::ensures(#iris "
    freeable_nz ptr
      (ly_size (use_layout_alg' Node_sls))
      1 HeapAlloc
")]
fn make_node(value: i32) -> *mut Node {
    let b = Box::new(Node { value });
    Box::into_raw(b)
}


#[rr::refined_by("(vals, locs)" : "(list Z * list loc)")]
#[rr::depend_on(Node)]
#[rr::inv("Hlen" : "length locs = length vals")]
#[rr::inv(#iris "
  ([∗ list] i ↦ v ∈ vals,
    ∃ l : loc,
      ⌜locs !! i = Some l⌝ ∗
      guarded true
        (l ◁ₗ[π, Owned]
          # -[#v]
          @ ◁(Node_ty <INST!>)) ∗
      freeable_nz l
        (ly_size (use_layout_alg' Node_sls))
        1 HeapAlloc)
")]
struct Heap {
    #[rr::field("(<#> locs)")]
    all_nodes: Vec<*mut Node>,
}

// 1つだけのポインタでもだめ？自動でやってくれない境界線はどこか
// Heap_alloc_lemma の定義
// Codex，前方の内容を記憶できているか


impl Heap {

    #[rr::returns("([], [])")]
    fn new() -> Self {
        Heap {
            all_nodes: Vec::new(),
        }
    }


    #[rr::params("h", "v" : "Z")]
    #[rr::args("h", "v")]
    #[rr::requires("MinInt i32 ≤ v")]
    #[rr::requires("v ≤ MaxInt i32")]
    #[rr::requires("
        let '(vals, locs) := h.cur in
        length locs < MaxInt usize
    ")]
    #[rr::requires("
        let '(vals, locs) := h.cur in
        size_of_array_in_bytes PtrSynType (2 * length locs) ≤ MaxInt isize
    ")]
    #[rr::exists("ptr" : "loc")]
    #[rr::returns("ptr")]
    #[rr::observe("h.ghost" : "
        let '(vals, locs) := h.cur in
        (vals ++ [v], locs ++ [ptr])
    ")]
    #[rr::ensures("ptr.(loc_a) ≠ 0")]
    fn alloc(&mut self, value: i32) -> *mut Node {
        let ptr = make_node(value);
        self.all_nodes.push(ptr);
        ptr
    }
}


fn main() {
    println!("Hello, world!");
}
