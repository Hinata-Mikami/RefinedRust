#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]
#![allow(unused)]
#![allow(non_camel_case_types)]
#![allow(unsafe_op_in_unsafe_fn)]

#![feature(stmt_expr_attributes)]

#![rr::include("stdlib")]
#![rr::include("vec")]
#![rr::include("option")]
#![rr::include("ptr")]
#![rr::include("mem")]
#![rr::include("rr_internal")]

#![rr::import("hinata_mikami.extra_proofs.gc", "heap_lemmas")]
#![rr::import("hinata_mikami.extra_proofs.gc", "gc_defs")]


use std::ptr;


use wrappers::*;

mod wrappers {
    #[rr::only_spec]
    #[rr::requires("index < length x")]
    #[rr::returns("x !!! Z.to_nat index")]
    pub fn vec_index<T>(x: &Vec<T>, index: usize) -> &T {
        &x[index]
    }

}

// 本質的には同じはずなのにNode側に書けないことは欠点
// 記録しておくべき
// 修論の一部にするくらいのつもりで 文章の形に
struct Node {
    value: i32,
    next: *mut Node,
    marked: bool,
}


impl Node{
    #[rr::params("node" : "loc", "next" : "loc", "v" : "Z", "old_next" : "loc", "m" : "bool")]
    #[rr::args("node", "next")]
    #[rr::requires(#type "node" : "-[#v; #old_next; #m]" @ "(Node_ty <INST!>)")]
    #[rr::ensures(#type "node" : "-[#v; #next; #m]" @ "(Node_ty <INST!>)")]
    #[rr::returns("()")]
    unsafe fn set_next(node: *mut Node, next: *mut Node) {
            (*node).next = next;
    }


    // ヘルパー
    #[rr::params(
        "node" : "loc",
        "v" : "Z",
        "next" : "loc",
        "old_m" : "bool",
        "new_m" : "bool"
    )]
    #[rr::args("node", "new_m")]
    #[rr::requires(
        #type "node" :
        "-[#v; #next; #old_m]" @ "(Node_ty <INST!>)"
    )]
    #[rr::ensures(
        #type "node" :
        "-[#v; #next; #new_m]" @ "(Node_ty <INST!>)"
    )]
    #[rr::returns("()")]
    unsafe fn set_marked(node: *mut Node, new_m: bool) {
        (*node).marked = new_m;
    }

}

// ここに inv を書かないほうがいい可能性も？関数側に書く方がいい傾向もあるか
#[rr::refined_by("(vals, locs, nexts, marks)" :
                 "(list Z * list loc * list loc * list bool)")]
#[rr::depends_on(Node)]
#[rr::inv("Hlen_locs" : "length locs = length vals")]
#[rr::inv("Hlen_nexts" : "length nexts = length vals")]
#[rr::inv("Hlen_marks" : "length marks = length vals")]
#[rr::inv("Hnext_valid" : "Forall (λ n, n = NULL_loc ∨ n ∈ locs) nexts")]
#[rr::inv(#iris "
  ([∗ list] i ↦ v ∈ vals,
    ∃ l n : loc, ∃ m : bool,
      ⌜locs !! i = Some l⌝ ∗
      ⌜nexts !! i = Some n⌝ ∗
      ⌜marks !! i = Some m⌝ ∗
      guarded true
        (l ◁ₗ[π, Owned]
          # -[#v; #n; #m] 
          @ ◁(Node_ty <INST!>)) ∗
      freeable_nz l
        (ly_size (use_layout_alg' Node_sls))
        1 HeapAlloc)
")]
#[rr::inv("Hnodup_locs" : "NoDup locs")]
// Needed to ensure we can turn ownership into a Box again for deallocation.
#[rr::inv("Hnot_null" : "Forall (λ l, l.(loc_a) ≠ 0) locs")]
struct Heap {
    #[rr::field("<#> locs")]
    all_nodes: Vec<*mut Node>,
}

// ヘルパー
#[rr::params("v" : "Z")]
#[rr::args("v")]
#[rr::requires("MinInt i32 ≤ v")]
#[rr::requires("v ≤ MaxInt i32")]
#[rr::exists("l" : "loc")]
#[rr::returns("l")]
#[rr::ensures(#type "l" : "-[#v; #NULL_loc; #false]" @ "(Node_ty <INST!>)")]
#[rr::ensures(#iris "freeable_nz l (ly_size (use_layout_alg' Node_sls)) 1 HeapAlloc")]
#[rr::ensures("l.(loc_a) ≠ 0")]
#[rr::ensures("MinInt usize ≤ l.(loc_a)")]
#[rr::ensures("l.(loc_a) ≤ MaxInt usize")]
fn make_node(v: i32) -> *mut Node {
    let node = Box::new(Node {
        value: v,
        next: ptr::null_mut(),
        marked: false,
    });
    Box::into_raw(node)
}

#[rr::params(
    "node" : "loc",
    "next" : "loc",
    "v" : "Z",
    "m" : "bool",
    "next_v" : "Z",
    "next_next" : "loc",
    "next_m" : "bool"
)]
#[rr::args("node")]
#[rr::requires("next.(loc_a) ≠ 0")]
#[rr::requires(#type "node" : "-[#v; #next; #m]" @ "(Node_ty <INST!>)")]
#[rr::requires(#type "next" : "-[#next_v; #next_next; #next_m]" @ "(Node_ty <INST!>)")]
#[rr::ensures(#type "node" : "-[#v; #next; #m]" @ "(Node_ty <INST!>)")]
#[rr::ensures(#type "next" : "-[#next_v; #next_next; #next_m]" @ "(Node_ty <INST!>)")]
#[rr::returns("next_v")]
unsafe fn read_next_value(node: *mut Node) -> i32 {
    let next = unsafe { (*node).next };
    unsafe { (*next).value }
}



impl Heap {
    #[rr::returns("([], [], [], [])")]
    fn new() -> Self {
        Heap {
            all_nodes: Vec::new(),
        }
    }

    //x' @ StructLtype +[◁ int i32; ◁ alias_ptr_t; ◁ bool_t] Node_sls を 
    //Node_ty に畳めないエラー? -> 手動証明でOK 
    #[rr::params("h", "v" : "Z")]
    #[rr::args("h", "v")]
    #[rr::requires("MinInt i32 ≤ v")]
    #[rr::requires("v ≤ MaxInt i32")]
    #[rr::requires("
        let '(vals, locs, nexts, marks) := h.cur in
        length locs < MaxInt usize
    ")]
    #[rr::requires("
        let '(vals, locs, nexts, marks) := h.cur in
        size_of_array_in_bytes PtrSynType (2 * length locs) ≤ MaxInt isize
    ")]
    #[rr::exists("ptr" : "loc")]
    #[rr::returns("ptr")]
    #[rr::observe("h.ghost" : "
        let '(vals, locs, nexts, marks) := h.cur in
        (vals ++ [v], locs ++ [ptr], nexts ++ [NULL_loc], marks ++ [false])
    ")]
    #[rr::ensures("ptr.(loc_a) ≠ 0")]
    fn alloc(&mut self, value: i32) -> *mut Node {
        let ptr = make_node(value);
        self.all_nodes.push(ptr);
        ptr
    }


    #[rr::params("h")]
    #[rr::args("h")]
    #[rr::requires("
        let '(vals, locs, nexts, marks) := h.cur in
        0 < length locs
    ")]
    #[rr::observe("h.ghost" : "
        let '(vals, locs, nexts, marks) := h.cur in
        (vals, locs, nexts, <[0%nat := true]> marks)
    ")]
    #[rr::returns("()")]
    unsafe fn mark_one(&mut self) {
        let node = *vec_index(&self.all_nodes, 0);
        Node::set_marked(node, true);
    }


    // mark の再帰呼び出し部分
    #[rr::params("h", "i" : "nat", "l" : "loc")]
    #[rr::args("h", "l")]
    #[rr::requires("
        let '(vals, locs, nexts, marks) := h.cur in
        locs !! i = Some l
    ")]
    #[rr::exists("marks_new" : "list bool")]
    #[rr::observe("h.ghost" : "
        let '(vals, locs, nexts, marks) := h.cur in
        (vals, locs, nexts, marks_new)
    ")]
    #[rr::ensures("
        let '(vals, locs, nexts, marks) := h.cur in
        mark_from_rel locs nexts marks i marks_new
    ")]
    #[rr::returns("()")]
    unsafe fn mark_from(&mut self, start_node: *mut Node) {

        // 一時的な proof-debug 用
        let _dummy = *vec_index(&self.all_nodes, 0);

        if (*start_node).marked {
            return;
        }

        let next = (*start_node).next;

        Node::set_marked(start_node, true);

        if !next.is_null() {
            self.mark_from(next);
        }

    }


    #[rr::params("h")]
    #[rr::args("h")]
    #[rr::requires("
        let '(vals, locs, nexts, marks) := h.cur in
        0 < length locs
    ")]
    #[rr::requires("
        let '(vals, locs, nexts, marks) := h.cur in
        all_unmarked marks
    ")]
    #[rr::exists("marks_new" : "list bool")]
    #[rr::observe("h.ghost" : "
        let '(vals, locs, nexts, marks) := h.cur in
        (vals, locs, nexts, marks_new)
    ")]
    #[rr::ensures("
        let '(vals, locs, nexts, marks) := h.cur in
        mark_from_rel locs nexts marks 0%nat marks_new
    ")]
    #[rr::ensures("
        let '(vals, locs, nexts, marks) := h.cur in
        marks_closed locs nexts marks_new
    ")]
    #[rr::returns("()")]
    #[rr::ensures("
        let '(vals, locs, nexts, marks) := h.cur in
        forall i,
        marks_new !! i = Some true <->
        reachable locs nexts i
    ")]
    unsafe fn mark(&mut self) {
        let root = *vec_index(&self.all_nodes, 0);
        self.mark_from(root);
    }


    // この辺の苦労はまとめておく
    // 実行時オーバーヘッドがある場合も実行して比較できればベスト（case_study）
    /* sweep annotation */
    #[rr::params(
        "vals"  : "list Z",
        "locs"  : "list loc",
        "nexts" : "list loc",
        "marks" : "list bool",
        "γ"
    )]
    // &mut xのrefinementは (-[x], γ)
    #[rr::args(#raw "((-[locs]), γ)")] // ここを変えるとなぜHeap_invが適用されなくなるか？という確認も欲しい

    /* 開始時：Heap invariant 成立 */
    #[rr::requires("length locs = length vals")]
    #[rr::requires("length nexts = length vals")]
    #[rr::requires("length marks = length vals")]
    #[rr::requires("Forall (λ n, n = NULL_loc ∨ n ∈ locs) nexts")]
    #[rr::requires("NoDup locs")]
    #[rr::requires("Forall (λ l, l.(loc_a) ≠ 0) locs")]
    #[rr::requires(#iris "
    ([∗ list] i ↦ v ∈ vals,
        ∃ l n : loc, ∃ m : bool,
        ⌜locs !! i = Some l⌝ ∗
        ⌜nexts !! i = Some n⌝ ∗
        ⌜marks !! i = Some m⌝ ∗
        guarded true
            (l ◁ₗ[π, Owned]
            # -[#v; #n; #m]
            @ ◁(Node_ty <INST!>)) ∗
        freeable_nz l
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc)
    ")]
    // mark : true かつ next が存在するなら next も mark : true
    // A[true] → B[false] でBを解放するとdangling pointerになる
    #[rr::requires("marks_closed locs nexts marks")]

    /* 事後条件 */
    /* keep_marked xs marks ... xs のうち marks が true のものだけを残す */
    // 終了後の locs' は locs[i] のうち marks[i] が true のもの
    #[rr::observe("γ": "
    let locs' := keep_marked locs marks in
    (-[# (<#> locs')] : plistRT [_])
    ")]

    /* invariant としていたものの構築 */
    // vals', nexts' も同様
    // locs'/nexts' と vals' の長さは同じ
    #[rr::ensures("
    let vals' := keep_marked vals marks in
    let locs' := keep_marked locs marks in
    length locs' = length vals'
    ")]
    #[rr::ensures("
    let vals' := keep_marked vals marks in
    let nexts' := keep_marked nexts marks in
    length nexts' = length vals'
    ")]
    #[rr::ensures("
    let locs' := keep_marked locs marks in
    NoDup locs'
    ")]
    #[rr::ensures("
    let locs' := keep_marked locs marks in
    Forall (λ l, l.(loc_a) ≠ 0) locs'
    ")]
    // 更新後の所有権
    // marks' は false を locs' 分複製
    #[rr::ensures(#iris "
    let vals' := keep_marked vals marks in
    let locs' := keep_marked locs marks in
    let nexts' := keep_marked nexts marks in
    let marks' := replicate (length locs') false in

    ([∗ list] i ↦ v ∈ vals',
        ∃ l n : loc, ∃ m : bool,
        ⌜locs' !! i = Some l⌝ ∗
        ⌜nexts' !! i = Some n⌝ ∗
        ⌜marks' !! i = Some m⌝ ∗
        guarded true
            (l ◁ₗ[π, Owned]
            # -[#v; #n; #m]
            @ ◁(Node_ty <INST!>)) ∗
        freeable_nz l
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc)
    ")]
    /*
    * sweep 中は壊してよいが、終了時には
    * live node だけに絞った locs'/nexts' について
    * Hnext_valid が再成立する。
    */
    #[rr::ensures("
    let locs' := keep_marked locs marks in
    let nexts' := keep_marked nexts marks in
    Forall
        (λ n, n = NULL_loc ∨ n ∈ locs')
        nexts'
    ")]

    /* 
        ループ内で毎回 &mut self.all_nodes を借用すると、
        そのたびに新しい一時 lifetime (κ, κ0, …) ができて 
        self の型の中に ShrBlockedLtype が積み重なり，検証が困難に。
        ループの外で一度だけ借用しておく形に変更
    */

    #[rr::returns("()")]
    unsafe fn sweep(&mut self) {
        let nodes = &mut self.all_nodes;
        let mut i = nodes.len();

        while i > 0 {
            let _ =
                #[rr::params("γnodes" : "gname")]
                #[rr::exists("ic" : "Z")]
                #[rr::inv_var("i" : "#ic")]
                /*
                * local_nodes の実際の refinement は概ね
                *
                *   # (
                *       # (<#> <$#> current_locs),
                *       γnodes
                *     )
                *
                * という形。
                */
                #[rr::inv_var("nodes" : "
                    # (
                        # (<#> <$#>
                            (keep_marked_suffix
                                (Z.to_nat ic)
                                locs
                                marks)),
                        γnodes
                    )
                ")]
                #[rr::inv("(0 ≤ ic ≤ length locs)%Z")]
                #[rr::inv(#iris "
                    sweep_nodes_inv
                        (Z.to_nat ic)
                        vals
                        locs
                        nexts
                        marks
                        (λ (v : Z)
                        (l n : loc)
                        (m : bool),
                            guarded true
                                (l ◁ₗ[π, Owned]
                                    # -[#v; #n; #m]
                                    @ (◁ (Node_ty <INST!>))) ∗
                            freeable_nz l
                                (ly_size
                                    (use_layout_alg' Node_sls))
                                1 HeapAlloc)
                ")]
                #[rr::ignore] || {};

            i -= 1;

            let node_ptr = *vec_index(nodes, i);

            if (*node_ptr).marked {
                /*
                * 生存ノード。
                * 後段のループで一括リセットする代わりに、
                * ここで false に戻す。
                */
                Node::set_marked(node_ptr, false);
            } else {
                // removeの戻り値の仕様に依存せず、直前に読んだ同じポインタを使う。
                let _ = nodes.remove(i);
                let _ = Box::from_raw(node_ptr);
            }
        }
    }


    /* マークアンドスイープGC */
    unsafe fn collect(&mut self) {
        println!("------------------------\nGC msg : Collection started.");

        self.mark();

        self.sweep();

        println!(
            "GC msg : Collection finished (alive: {}).\n------------------------",
            self.all_nodes.len()
        );
    }


    unsafe fn print_heap(&self) {
        for &ptr in &self.all_nodes {
            print!("[{}] ", (*ptr).value);
        }
        println!();
    }
}

fn main() {
}
