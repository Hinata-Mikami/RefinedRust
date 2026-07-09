
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


#[rr::refined_by("()" : "unitRT")]
#[rr::exists("x")]
#[rr::only_spec(drop_glue)]
struct Foo {
    #[rr::field("x")]
    x: Option<Bar>,
}

#[rr::refined_by("()" : "unitRT")]
struct Bar {
    #[rr::field("#tt")]
    x : Box<Foo>,
}

/*
#[rr::refined_by("list (place_rfn {rt_of T})")]
#[rr::only_spec(drop_glue)]
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


#[rr::refined_by("option unit")]
#[rr::only_spec(drop_glue)]
enum Bla {
    #[rr::pattern("None")]
    BlaV,
    #[rr::pattern("Some" $ "x")]
    #[rr::refinement("x")]
    #[rr::refined_by("x" : "unitRT")]
    BlaW(#[rr::field("#x")] Box<Blub>),
}

#[rr::refined_by("()" : "unitRT")]
#[rr::exists("x")]
struct Blub {
    #[rr::field("x")]
    x : Bla, 
}
