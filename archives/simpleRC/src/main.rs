#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

// sub functions
#[rr::trusted]
#[rr::params("x", "T")]
#[rr::args("(0, x)")]
#[rr::returns("(0, x)")]
fn box_new<T>(t: T) -> Box<T> {
    Box::new(t)
}

#[rr::trusted]
#[rr::params("x", "T")]
#[rr::args("x" @ "T")]
#[rr::exists("l", "c")]
#[rr::returns("l")]
#[rr::ensures(#type "l" : "(c, x)" @ "int i32 * T")] 
fn box_into_raw<T>(b: Box<T>) -> *mut T {
    Box::into_raw(b)
}

#[rr::trusted]
#[rr::params("l", "x")]
#[rr::args("l")]
#[rr::exists("T")]
#[rr::requires(#type "l" : "(0, x)" @ "int i32 * T")] 
#[rr::returns("(0, x)")]
unsafe fn box_from_raw<T>(ptr: *mut T) -> Box<T> {
    Box::from_raw(ptr)
}

// ヒープ領域に確保されるデータ
#[rr::refined_by("(c, x)")]
#[rr::invariant("1 <= c")]
// rc>=1ならば data が有効
struct RcInner<T> {
    #[rr::field("c" @ "int i32")]
    count: usize,
    #[rr::field("x")]
    data: T,
}

// ユーザが使用するスマートポインタ
#[rr::refined_by("l")]
#[rr::exists("c", "x", "T")]
#[rr::invariant(#type "l" : "(c, x)" @ "int i32 * T")]
// RcInnerのrc >= 1 
struct SimpleRC<T> {
    #[rr::field("l")]
    ptr: *mut RcInner<T>,
}
// simpleRC の数 (RcInnerを参照している数) == RcInner.count

impl<T> SimpleRC<T> {
    
    #[rr::params("x", "T")]
    #[rr::args("x" @ "T")]
    #[rr::exists("l", "c")]
    #[rr::returns("l")]
    // TODO : 事後条件
    #[rr::ensures(#type "l" : "(c, x)" @ "int i32 * T")]
    #[rr::ensures("c = 1")]
    
    fn new(data: T) -> Self {

        let inner = RcInner {
            count: 1,
            data,
        };
        
        let boxed = box_new(inner);

        let ptr = box_into_raw(boxed);

        return SimpleRC { ptr };
    }

    // 現在の参照カウントを取得
    pub fn rc_count(&self) -> usize {
        return unsafe { (*self.ptr).count }
    }

    // 
    pub fn read_from(&self) -> &T {
        // 絶対に rc >= 1
        return unsafe { &(*self.ptr).data }
    }
}

// Clone トレイトの実装
// 参照カウントをインクリメントし，新しい SimpleRC を返す
impl<T> Clone for SimpleRC<T> {
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
impl<T> Drop for SimpleRC<T> {
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
    let a = SimpleRC::new('a');

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



// &mut をとるとうまくいかなくなる最小の例を残しておく