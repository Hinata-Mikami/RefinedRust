# Documentation of the shim interface

This documentation for RefinedRust developers documents which identifiers are exported through `rrlib` shims that RefinedRust generates as the summary of a processed crate.
These identifiers refer to Rocq definitions that the verification of other crates can rely on.

The interface is structured as a JSON file of the following shape:
```
{
  // The name of the module, as used in rr::include annotations
  "refinedrust_name": String,
  // The Rocq module path to the generated Rocq module
  "refinedrust_path": String, 
  // The Rocq module name of the module containing the spec definitions
  "refinedrust_module": String,
  // other Rocq modules this module depends on
  "module_dependencies": list String,
  // other RefinedRust modules this module exports (as used in rr::export_include)
  "export_libs": list String,
  // the items of this module
  "items": list Item,
}
```

Each `Item` is one of the following:

## ADTs

```
{
  "kind": "adt",
  // the rustc path
  "path": Path,
  // the refinement type definition
  "rtype": Ident,
  // the semantic type definition
  "semtype": Ident,
  // the syntactic type definition
  "syntype": Ident,
  // more internal information about the spec
  "info": AdtShimInfo
}
```


## Trait
```
{
  "kind": "trait",
  // the rustc path
  "path": Path,
  // the base name
  "name": String,
  // maps methods to their trait_incl declaration
  "method_trait_incl_decls": Map<String, Ident>,
  /// whether this trait has a semantic interpretation
  "has_semantic_interp": bool,
  // allowed spec attributes
  "allowed_attrs": Vec<String>,
  // whether the attrs record is dependent
  "attrs_dependent": bool,
},
```

From the base name `name`, several other exported identifiers are implicitly derived:
- `base_spec`: `{name}_base_spec`
- `spec_attrs_record`: `{name}_spec_attrs`
- `spec_record`: `{name}_spec`
- `spec_subsumption`: `{name}_spec_incl`
- if `has_semantic_interp` is `true`, then `spec_semantic`: `{name}_semantic_interp`

## Functions
```
{
  kind: "function" or "method",
  // the base name
  "name": String,
  // the rustc path
  path: Path,
  
  // the Rocq name of the spec
  spec: Ident,
  // the Rocq name of the trait assumption inclusion for this function
  trait_req_incl: Ident
}
```

## Trait impl

```
{ 
  kind: "trait_impl",
  // The rustc path for the trait
  trait_path: PathWithArgs,
  // for which type is this implementation?
  for_type: Type,

  // map from method names to (base name, specification name, trait incl name)
  method_specs: Map<String, (String, String, String)>,

  specs: LiteralImpl,
```

where 
```
LiteralImpl = 
{
    "name": String,
    // Whether is there a Rocq definition name for the trait's semantic interpretation.
    "has_semantic_interp": bool,
}
```

From the base name `name`, several other exported identifiers are implicitly derived:
- `spec_record`: `{name}_spec`
- `spec_attrs_record`: `{name}_spec_attrs`
- `spec_subsumption_statement`: `{name}_spec_incl`
- if `has_semantic_interp` is `true`, then `spec_semantic`: `{name}_semantic_interp`
- `spec_subsumption_proof`: `{name}_spec_subsumption_correct`
- `spec_subsumption_statement`: `{name}_spec_subsumption}`


## Auxiliary types
```
type Path = Vec<String>
type PathWithArgs = (Path, Vec<Option<Type>>)

type Type
type AdtShimInfo
```
