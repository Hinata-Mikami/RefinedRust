# Overview of attributes

Rust code can be annotated with attributes to provide specifications and other information to RefinedRust.
All RefinedRust attributes are prefixed with the name space `rr`.

## Function attributes
As an example, the following function has specifications attached to it that say that it adds `42` to an integer:

```rust
#[rr::params(z)]
#[rr::args("z")]
#[rr::requires("z + 42 ∈ i32")]
#[rr::returns("z + 42")]
fn add_42(x : i32) -> i32 {
  x + 42
}
```
The `params` clause specifies a universally-quantified parameter of the specification -- in this case, the (mathematical) integer `z` represented by the argument `x`.

The `args` clause specifies the refinement and (optionally) a type for the single argument `x` of the function.
RefinedRust infers a "default" type for the argument from Rust's type, but this can also be overridden by providing an explicit type after a `@`.
For instance, the clause `#[rr::args("z" @ "int i32")]` would be equivalent to the one specified above.
In addition, for types (like structs) with invariants declared on them, the argument can be prefixed with `#raw` in order to not require the invariant on them to hold (e.g. `#[rr::args("z", #raw "-[x]")]`).

The `requires` clause specifies the requirement that the result of the addition fits into an `i32` (see [RefinedRust propositions](#refinedrust-propositions) for details on the syntax).

Finally, the `returns` clause specifies a refinement (and optionally, a type) for the return value of the function.

### Shortcut attributes
As an alternative to specifying the refinement for arguments explicitly, we can also let RefinedRust automatically introduce a parameter for them.
If the `rr::args` clause is missing, RefinedRust will automatically introduce one parameter for every argument, named after the Rust variable name, and assume that the arguments are refined accordingly.
For instance, we can equivalently specify the `add_42` as:
```rust
#[rr::requires("x + 42 ∈ i32")]
#[rr::returns("x + 42")]
fn add_42(x : i32) -> i32 {
  x + 42
}
```
For mutable reference arguments `x`, you can use the notations `x.cur` and `x.ghost` to refer to the references current value and ghost variable, respectively.


| Keyword   | Purpose                      | Properties | Example                          |
|-----------|------------------------------|------------|----------------------------------|
| `params`  | specify Rocq-level specification parameters | multiple   | `#[rr:params("n" : "Z", b : "bool")]` |
| `param`  | specify Rocq-level parameters | multiple   | `#[rr:param("n" : "Z")]` |
| `args`    | specify argument refinements/types | multiple | `#[rr::args("n" @ "int i32", "b"]` |
| `returns` | specify return refinement/type | single | `#[rr::returns("42" @ "int i32")]` |
| `requires` | specify a precondition | multiple | `#[rr:requires("i > 42")]` |
| `ensures` | specify a postcondition | multiple | `#[rr::ensures("x > y")]` |
| `exists`  | specify an existential for the postcondition | multiple | `#[rr::exists("x" : "Z")]` |
| `observe` | shortcut for specifying observations on ghost variables | single | `#[rr::observe("γ": "x + 2")]` |
| `context` | add an unnamed implicit parameter to the context | single | `#[rr::context("ghost_varG Σ Z")]` |
| `shim`  | replace the function with a shim with the given code an specification | single | `#[rr::shim("ptr_dangling", "type_of_ptr_dangling")]` |

There are further attributes that influence the proof-checking behaviour:
| Keyword   | Purpose                      | Properties | Example                          |
|-----------|------------------------------|------------|----------------------------------|
| `verify`  | Tell RefinedRust to verify this function with the default specification | none | `#[rr::verify]` |
| `trust_me`  | generate and type-check the specification and code, but do not generate a proof | none   | `#[rr::trust_me]` |
| `only_spec`  | only generate and type-check the specification, but do not generate the code | none   | `#[rr::only_spec]` |
| `skip`  | ignore annotations on this function completely | none   | `#[rr::skip]` |
| `export_as` | influence the exported path in the generated RefinedRust library interface for import in other proofs | a Rust path | `#[rr::export_as(std::vec::Vec::push)]` |

## Closure attributes
RefinedRust has support for closures.
The same attributes as for functions apply, but in addition, you can specify assumptions and modifications on the captures of the closure.
For this, you can use escape sequences (see [Escape sequences](#escape-sequences) below) to refer to the captures of the closure by their Rust names.
For instance, if the closure captures variable `x`, you can use `{x}` to refer to its mathematical value.
If the closure captures `x` *mutably*, you can additionally use `{x.*new}` to refer to its *new* value in the postcondition.

If capturing a place which is not a variable, this syntax also works for place projections which are captured; for instance, you may use `{x.a.b}` or `{(*x).a.b.*new}`.

## Impl attributes
The following attributes are also available on impls and then influence all functions contained in them:
| Keyword   | Purpose                      | Properties | Example                          |
|-----------|------------------------------|------------|----------------------------------|
| `export_as` | influence the exported paths in the generated RefinedRust library interface for import in other proofs | a Rust path | `#[rr::export_as(std::vec::Vec)]` |
| `trust_me`  | generate and type-check the specifications and code, but do not generate proofs | none   | `#[rr::trust_me]` |
| `only_spec`  | only generate and type-check the specifications, but do not generate the code | none   | `#[rr::only_spec]` |
| `skip`  | ignore this block completely | none   | `#[rr::skip]` |
| `context` | add an unnamed implicit parameter to the context | single | `#[rr::context("ghost_varG Σ Z")]` |


## Struct attributes
| Keyword   | Purpose                      | Properties | Example                          |
|-----------|------------------------------|------------|----------------------------------|
| `refined_by` | Specify the refinement type of a struct | single | `#[rr::refined_by("(a, b, l)" : "(Z * Z * loc)")]` |
| `exists` | Specify an existentially abstracted mathematical value | multiple | `#[rr::exists("x" : "Z")]` |
| `invariant` | Specify an invariant on the struct type | multiple | `#[rr::invariant("#type "l" : "x" @ "int i32")]` |
| `refines` | Optionally specify the refinement of the raw struct type (can only be used when no refinements are specified via `field` attributes on the struct's fields) | single | `#[rr::refines("-[a; b]")]` |
| `mode`  | Specifies the sharing mode of the defined type: either `plain` (the default, invariants are shared on a best-effort basis for the sharing invariant) or `persistent` (all invariants need to be shareable) | `#[rr::mode("plain")]` |
| `export_as` | influence the exported path in the generated RefinedRust library interface for import in other proofs | a Rust path | `#[rr::export_as(std::vec::Vec)]` |
| `context` | add an unnamed implicit parameter to the context in which the invariant is declared | single | `#[rr::context("ghost_varG Σ Z")]` |

Invariants on structs can be prefixed by `#own` or `#shr` to only include the invariant in the struct's ownership or sharing predicate, respectively, e.g.: `#[rr::invariant(#own "freeable l len")]`.

Struct fields can be annotated with a `field` attribute specifying the struct field's type and refinement in one of the following forms:
- `#[rr::field("l" @ "alias_ptr_t")]`, specifying a refinement and a type. No `refines` attribute should have been specified on the struct.
- `#[rr::field("l")]`, specifying just a refinement. No `refines` attribute should have been specified on the struct.
- `#[rr::field("alias_ptr_t")]`, specifying just a type. A `refines` attribute needs to have been specified on the struct.

## Enum attributes
Enums have a top-level `refined_by` attribute for specifying the enum's refinement type.
Each of the enum's variants is annotated with two attributes:
- a `pattern` attribute for matching on the enum's refinement type
- a `refinement` attribute for specifying the refinement of the variant's component type, often a tuple type.
  If a variant contains a nested struct, the struct can further be annotated with all the usual struct attributes.

For instance, the `option` type could be specified as follows, being refined by Rocq's `option` type.
```rust
#[rr::refined_by("option (place_rfn {rt_of T})")]
enum option<T> {
    #[rr::pattern("None")]
    #[rr::refinement("-[]")] // can be left implicit
    None,
    #[rr::pattern("Some" $ "x")]
    #[rr::refinement("-[x]")]
    Some(T),
}
```

In addition, enums also support the `export_as` attribute (same as structs).

### Refinement generation
Instead of refining an enum with an existing Rocq type, RefinedRust can also generate a new Rocq type corresponding to the Rust enum declaration.
For this, the `rr::refine_as` attribute can be used used, which takes the desired Rocq name of the definition as its argument.

For instance:
```
#[rr::refine_as("option")]
enum option<T> {
    None,
    Some(T),
}
```

## Static attributes
RefinedRust supports `static` (but currently not `static mut`) variables.
They can be used as if they were behind a shared reference with `static` lifetime.

For a static variable to be used by the RefinedRust type checker, the respective function needs to require it to be initialized,
using the `initialized π "name" r` predicate, where `r` is the assumed refinement of the static variable.
To specify the name that is used to refer to the variable here, `static` variables can be annotated with a `rr::name` attribute:
- `#[rr::name("my_static_int")]` indicates that the name `my_static_int` should be used to refer to the static in specifications.

## Trait attributes
Traits can have additional "specification attributes" which are instantiated by impls.
The generic specification of trait methods can mention these specification attributes in order to be parameterizable over implementations.

To specify an attribute, trait declarations can be annotated with a `rr::exists` attribute:
- `#[rr::exists("Done" : "{rt_of Self} → Prop")]` indicates that an attribute `Done` of the given Rocq type should be declared, using the escape sequences explained below.

For further specifications in the trait declaration (e.g. for the specification of the trait's methods), the name `Done` will be in scope, enclosed with braces (e.g. `{Done}`).
The attribute declarations can depend on each other in the definition order, e.g. it would be valid to specify:
`#[rr::exists("DoneDec" : "∀ x, Decision {Done}")]`

## Trait impl attributes
Trait implementations have to instantiate the specification attributes declared on the trait they're implementing, using `rr::instantiate` attributes:
- `#[rr::instantiate("Done" := "λ _, True")]` indicates that the `Done` attribute should be instantiated with the given term for this impl.

In the proof of the specifications for the trait's methods, this instantiation is assumed.

## Module attributes
Inside a module, the following mod-level attributes can be specified:
- `#![rr::import("A.B.C", "D")]`: imports the file `D` from logical Rocq path `A.B.C` in all spec and proof files
- `#![rr::include("vec")]`: imports the RefinedRust library `vec` from the loadpath

## Crate attributes
Inside a crate, the following crate-level attributes can be specified:
- `#![rr::coq_prefix("A.B.C")]`: puts the generated files under the logical Rocq path `A.B.C`
- `#![rr::import("A.B.C", "D")]`: imports the file `D` from logical Rocq path `A.B.C` in all spec and proof files
- `#![rr::include("vec")]`: imports the RefinedRust library `vec` from the loadpath

## RefinedRust propositions
For propositional specifications, as appearing in `#[rr::requires("P")]`, `#[rr::ensures("P")]`, and `#[rr::invariant("P")]`, specific notational shortcuts are supported.
By default, `P` is interpreted as a (pure) Rocq proposition (i.e., it is interpreted to the Iris proposition `⌜P⌝`).

This can be changed by format specifiers starting with `#` which preceed the string `"P"`:

- The `#iris` format specifier interprets `P` as an Iris proposition.
- Type assignments for locations/places can be specified by the `#type "l" : "r" @ "ty"` template, specifying that `l` is an owned pointer storing a value of type `r @ ty`.
- In `rr::requires` clauses on functions, the `#linktime` specifier makes this a link-time assumption. This is useful for assumptions on the size of a datatype under the used layout algorithm. These assumptions do not become part of the set of preconditions one has to prove when calling this function, but instead have to be proved when linking the whole program together for a closed adequacy result.
- In `rr::invariant` clauses on structs, the `#own` specifier only makes the following Iris proposition available in the invariant for owned types.
- In `rr::invariant` clauses on structs, the `#shr` specifier only makes the following Iris proposition available in the invariant for shared types.

In the default interpretation as pure Rocq propositions, optionally a name can be specified that will be used in Rocq's context (if the proposition becomes a hypothesis), by writing (for instance) `#[rr::requires("Hx" : "x < 5")]`.
This is especially useful for semi-manual proofs.

## Special syntax
### Escape sequences
As a rule of thumb, all  string literals in specifications are inserted literally into the generated Rocq code.
However, specifications can escape into special syntax inside `{ }` (curly braces) in order to access some Rust-level variables.
These escape sequences are literally replaced by the frontend.
To prevent an expression wrapped in curly braces to be transformed, write two curly braces: `{{ ... }}`.
This will be replaced by `{ ... }`.

#### Types and lifetimes
In particular, we support the following escape sequences to refer to components of types and lifetimes:

| Example | Purpose |
|---------|---------|
| `{ty_of T}`   | Gets substituted by the RefinedRust type corresponding to the Rust type variable `T` |
| `{st_of T}` | Gets substituted by the syntactic type (providing layout information) of the type parameter `T` |
| `{ly_of T}` | Gets substituted by a term giving the layout of the type parameter `T`'s syntactic type |
| `{xt_of T}` | Gets substituted by the surface type (mathematical model) of the type parameter `T` |
| `{rt_of T}` | Gets substituted by the refinement type (mathematical model) of the type parameter `T` |
| `{'a}` | Gets replaced by a term describing the lifetime of lifetime parameter 'a |

Note that here, `T` can also refer to an associated type (of a trait requirement) of the form `T::Output` (where `Output` is an associated type on a trait requirement of `T`).
We currently do not support specifying as *which* trait this should be intepreted (`<T as Iterator>::Output`), so in some cases there may be name collisions.

#### Trait attributes
We can refer to declared specification attributes of traits in the same way as we refer to associated types.
For instance, if `T : Iterator`, then `{T::Next}` will refer to its `Next` relation.

#### Closure captures
In pre- and postconditions on closures, escape sequences can be used to refer to the captures of the closure by their Rust names.
For instance, if the closure captures variable `x`, you can use `{x}` to refer to its mathematical value.
If the closure captures `x` *mutably*, you can additionally use `{x.*new}` to refer to its *new* value in the postcondition.

If capturing a place which is not a variable, this syntax also works for place projections which are captured; for instance, you may use `{x.a.b}` or `{(*x).a.b.*new}`.

## On export behavior

Specifications for public definitions in a crate that RefinedRust verifies are exported through the automatically generated `interface.rrlib` files.
This file can be imported in other verified client crates through the `rr::include` attribute, so that the specifications are available and RefinedRust can use the exported types and functions.

For most exported definitions, an `rr::export_as` attribute can be used to influence the path under which they are exported.
This is particularly useful to provide axiomatized shims for libraries we don't want to verify (yet), but use as part of other verification projects.
Examples of this are provided in the `stdlib` folder, which provides axiomatized specifications for some libraries.

Currently, the following objects are exported:
- functions
- methods in impls
- ADTs (structs and enums)
- trait impls 

On importing a specification for a trait impl, if there are multiple candidate implementations this specification could attach to, a warning is issued.
This case should be avoided, as it is fragile; if you encounter such a case, file an issue, so that the disambiguation criteria can be improved.

## Types
TODO: provide an overview of RefinedRust types.
