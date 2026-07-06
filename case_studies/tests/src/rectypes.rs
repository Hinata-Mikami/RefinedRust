
#[rr::refined_by("()" : "unit")]
#[rr::exists("d" : "{xt_of T}")]
#[rr::exists("c" : "list unit")]
struct Tree<T: Eq> {
    #[rr::field("$# d")]
    data: T,
    #[rr::field("<#> c")]
    children: Vec<Tree<T>>,
}

impl<T: Eq> Tree<T> {
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn new(d: T) -> Self {
        Tree {
            data: d,
            children: Vec::new(),
        }
    }
}

/*
#[rr::refined_by("list (place_rfn {rt_of T})")]
enum List<T> {
    #[rr::pattern("[]")]
    Nil,
    #[rr::pattern("cons" $ "x", "xs")]
    #[rr::refinement("(x, xs)")]
    #[rr::refined_by("(x, xs)" : "(place_rfn {rt_of T}) * (list (place_rfn {rt_of T}))")]
    Cons(
        #[rr::field("x")]
        T, 
        #[rr::field("#xs")]
        Box<List<T>>),
}
*/
