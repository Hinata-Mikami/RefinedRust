// ——― RefinedRust annotations ——―//
#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
// ——― RefinedRust annotations END ——―//

fn main(){

}

fn logic() {
    let mut a;

    a = EvenInt::new(0);

    a.add_two();
    assert!(a.get() % 2 == 0);  // 検証したいこと
    
}

// RefinedRustの数理モデルはCoqの整数Zを使う
// この辺の話は SPEC_FORMAT.md に詳しく記載
#[rr::refined_by("x" : "Z")] // EvenInt は Coq integers "Z"
#[rr::invariant("Zeven x")]  // Zeven x : x が偶数であるというCoq上の述語（不変条件）
struct EvenInt {
    #[rr::field("x")]
    num: i32,
}

impl EvenInt {
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::requires("Zeven x")]
    #[rr::returns("x")]

    /// Create a new even integer.
    pub fn new(z: i32) -> Self {
        Self {num: z}
    }

    #[rr::params("x", "γ")]
    #[rr::args(#raw "(#(-[#x]), γ)")]   //#raw :EvenIntが持つ不変条件を満たさなくてもいいという意味
                                        // we use -[#x] for the contents of the mutable reference
                                        // γが指す場所に格納されている整数をxとする，ということ？
    #[rr::requires("(x + 1 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "(-[#(x+1)%Z] : plist place_rfn _)")] //事後条件（たぶん）

    // #[rr::params("x", "γ")]
    // #[rr::args(#raw "((-[x]), γ)")]
    // #[rr::requires("(x + 1 ≤ MaxInt i32)%Z")]
    // #[rr::observe("γ": "(-[#(x+1)%Z] : plistRT _)")]

    /// Internal function. Unsafely add 1, making the integer odd.
    fn add(&mut self) {
        self.num += 1;
    }

    /// Get the even integer
    pub fn get(&self) -> i32 {
        self.num
    }

    /// Add another even integer.
    // pub fn add_even(&mut self, other: &Self) {
    //     self.num += other.num;
    // }

    #[rr::params("x", "γ")]
    #[rr::args("(#x, γ)")]
    #[rr::requires("(x + 2 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "(x+2)")]
    /// Add 2 to an even integer.
    pub fn add_two(&mut self) {
        self.num;
        unsafe{
            self.add();
            self.add();
        }
    }
}



// add_two にアノテーションを追加したときのエラー
// x + 1 + 1 が偶数であることを証明できなかった
// こういう時は，手動でvファイルを編集して証明を通すこともできる
// この場合，sidecond_hammmer の後に
// { rewrite -Z.add_assoc; apply Zeven_plus_Zeven; solve_goal. }
// を追加


// 以下エラー文
// Shelved goal remaining in  "EvenInt_add_two" !
// Goal:
// FN_NAME : string
// EvenInt_sl : struct_layout
// H :
// (use_layout_alg
//    (StructSynType (sls_name EvenInt_sls) (sls_fields EvenInt_sls)
//       (sls_repr EvenInt_sls)) = Some EvenInt_sl)
// EvenInt_salg :
// (struct_layout_alg "EvenInt" [("num", i32)] StructReprRust = Some EvenInt_sl)
// H0 : (ly_size i32 ≤ MaxInt isize_t)
// H1 : (layout_wf EvenInt_sl)
// H2 : (ly_size EvenInt_sl ≤ MaxInt isize_t)
// H3 : (ly_align_in_bounds EvenInt_sl)
// fields_N : (sl_has_members EvenInt_sl [("num", i32)])
// H4 : (MaxInt isize_t < MaxInt usize_t)
// H5 : (127 ≤ MaxInt i8)
// H6 : (127 ≤ MaxInt u8)
// H7 : (127 ≤ MaxInt i16)
// H8 : (127 ≤ MaxInt u16)
// H9 : (127 ≤ MaxInt i32)
// H10 : (127 ≤ MaxInt u32)
// H11 : (127 ≤ MaxInt i64)
// H12 : (127 ≤ MaxInt u64)
// H13 : (127 ≤ MaxInt i128)
// H14 : (127 ≤ MaxInt u128)
// H15 : (127 ≤ MaxInt isize_t)
// H16 : (127 ≤ MaxInt usize_t)
// H17 : (MinInt i8 ≤ -128)
// H18 : (MinInt i16 ≤ -128)
// H19 : (MinInt i32 ≤ -128)
// H20 : (MinInt i64 ≤ -128)
// H21 : (MinInt i128 ≤ -128)
// H22 : (MinInt isize_t ≤ -128)
// H23 : (MinInt u8 = 0)
// H24 : (MinInt u16 = 0)
// H25 : (MinInt u32 = 0)
// H26 : (MinInt u64 = 0)
// H27 : (MinInt u128 = 0)
// H28 : (MinInt usize_t = 0)
// arg_self : loc
// local___0 : loc
// local___2 : loc
// local___3 : loc
// local___4 : loc
// local___5 : loc
// local___6 : loc
// x : Z
// H29 : (arg_self `has_layout_loc` void*)
// H30 : (0 < arg_self.2 - 0%nat)
// H31 : (arg_self.2 + bytes_per_addr ≤ MaxInt usize_t)
// H32 : (local___0 `has_layout_loc` unit_sl)
// H33 : (0 < local___0.2 - 0%nat)
// H34 : (local___0.2 + 0%nat ≤ MaxInt usize_t)
// H35 : (ly_size i32 ≤ MaxInt isize_t)
// H36 : (local___2 `has_layout_loc` i32)
// H37 : (0 < local___2.2 - 0%nat)
// H38 : (local___2.2 + bytes_per_int i32 ≤ MaxInt usize_t)
// H39 : (local___3 `has_layout_loc` unit_sl)
// H40 : (0 < local___3.2 - 0%nat)
// H41 : (local___3.2 + 0%nat ≤ MaxInt usize_t)
// H42 : (local___4 `has_layout_loc` void*)
// H43 : (0 < local___4.2 - 0%nat)
// H44 : (local___4.2 + bytes_per_addr ≤ MaxInt usize_t)
// H45 : (local___5 `has_layout_loc` unit_sl)
// H46 : (0 < local___5.2 - 0%nat)
// H47 : (local___5.2 + 0%nat ≤ MaxInt usize_t)
// H48 : (local___6 `has_layout_loc` void*)
// H49 : (0 < local___6.2 - 0%nat)
// H50 : (local___6.2 + bytes_per_addr ≤ MaxInt usize_t)
// H51 : (x + 2 ≤ MaxInt i32)
// H52 : (Zeven x)
// ---------------------------------------
// (Inhabited (Zeven (x + 1 + 1)))


// File "./case_studies/evenint/output/evenint/proofs/proof_EvenInt_add_two.v", line 21, characters 0-4:
// Error:  (in proof EvenInt_add_two_proof): Attempt to save a proof with given
// up goals. If this is really what you want to do, use Admitted in place of
// Qed.