#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

// sub functions
#[rr::only_spec]
#[rr::params("x")]
#[rr::args("x" @ "(RcInner_inv_t <INST!>)")] // RRにより自動生成された型
#[rr::returns("x" @ "(box (RcInner_inv_t <INST!>))")]
fn box_new(t: RcInner) -> Box<RcInner> {
    Box::new(t)
}

#[rr::only_spec]
#[rr::params("x")]
#[rr::args("x" @ "(box (RcInner_inv_t <INST!>))")]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures(#type "l" : "x" @ "(RcInner_inv_t <INST!>)")] 
fn box_into_raw(b: Box<RcInner>) -> *mut RcInner {
    Box::into_raw(b)
}

#[rr::only_spec]
#[rr::params("l", "x")]
#[rr::args("l")]
#[rr::requires(#type "l" : "x" @ "(RcInner_inv_t <INST!>)")] 
#[rr::returns("x" @ "(box (RcInner_inv_t <INST!>))")]
unsafe fn box_from_raw(ptr: *mut RcInner) -> Box<RcInner> {
    Box::from_raw(ptr)
}

// ヒープ領域に確保されるデータ
#[rr::refined_by("c" : "Z")]
#[rr::invariant("1 <= c")]
// rc>=1ならば data が有効
struct RcInner {
    #[rr::field("c")]
    count: usize,
}

// ユーザが使用するスマートポインタ
#[rr::refined_by("l" : "loc", "c" : "Z")]
#[rr::exists("c")] 
#[rr::invariant(#type "l" : "c" @ "(RcInner_inv_t <INST!>)")]
// #[rr::refined_by("l" : "loc")]
// #[rr::exists("c")]
// #[rr::invariant(#type "l" : "c" @ "(RcInner_inv_t <INST!>)")]
struct SimpleRC{
    #[rr::field("l")]
    ptr: *mut RcInner,
}

impl SimpleRC {
    
    // #[rr::exists("l")]
    // #[rr::args("l")]
    #[rr::exists("l", "c")]
    #[rr::returns("l", "c")]
    #[rr::ensures("c = 1")]
    fn new() -> Self {

        let inner = RcInner { count: 1,};
        let boxed = box_new(inner);
        let ptr = box_into_raw(boxed);

        return SimpleRC { ptr };
    }

    // 現在の参照カウントを取得
    #[rr::params("self")]
    #[rr::args("self")]
    #[rr::returns("self.2")]
    pub fn rc_count(&self) -> usize {
        return unsafe { (*self.ptr).count }
    }

}

// Clone トレイトの実装
// 参照カウントをインクリメントし，新しい SimpleRC を返す
impl Clone for SimpleRC {
    fn clone(&self) -> Self {
        unsafe {
            (*self.ptr).count += 1;
        }
        return SimpleRC { ptr: self.ptr };
    }
}

// Drop トレイトの実装
// 参照カウントをデクリメントし，0 になったらデータ管理を Box に戻す

// （優先度低）正しく解放されるのか？実際には何個の参照が存在するか（ghost）
impl Drop for SimpleRC {
    fn drop(&mut self) {
        unsafe {
            (*self.ptr).count -= 1;

            if (*self.ptr).count == 0 {
                let _ = box_from_raw(self.ptr);
            }
        }
    }
}



fn main(){
    let a = SimpleRC::new();

    assert!(a.rc_count() == 1); // Rc(a) = 1

    {
        let b = a.clone();
        let c = b.clone(); 
        assert!(a.rc_count() == 3); // Rc(a) = 3

        drop(c); 
        assert!(a.rc_count() == 2); // Rc(a) = 2

    }   // drop(b) が実行される

    assert!(a.rc_count() == 1); // Rc(a) = 1
}   // drop(a) が実行され，a が free される   
