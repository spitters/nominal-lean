# Nominal separation and binding in Iris

## Summary

This PR adds an Iris/BI layer on top of nominal-lean: a family of assertions in
iris-lean's classical heap model `HeapProp Unit` indexed by atoms, a permutation
action on that model, a name-allocation ghost state, and a simply-typed judgment
on α-quotiented terms whose freshness premise is discharged by that ghost state.
Atoms, name-worlds, and terms live in nominal-lean's `Atom` / `FinPerm` / `NomSet`;
the Iris layer (`NominalIris.*`) is built over those atoms.

`NomProp` is `HeapProp Unit`. The law below is the points-to disjointness law
`ℓ₁ ↦ () ∗ ℓ₂ ↦ () ⊢ ℓ₁ ≠ ℓ₂` of that model at unit values, with locations the
atoms' underlying numbers:

```lean
theorem freshName_sep_ne (a b : Atom) :
    (freshName a ∗ freshName b : NomProp) ⊢ iprop(⌜a ≠ b⌝)
```

The law is equivariant: `FinPerm` acts on all of `NomProp` (`permProp`), the image
of `freshName a` is `freshName (π a)` (`permProp_freshName`), and carrying the law
along the action gives the law at the image names (`freshName_sep_ne_perm`).

Two owned fresh names of the ghost state are distinct (`ownFresh_distinct`). The
denotation `den` is the resource-level link from the camera to `NomProp`
(`den_freshRA`, `den_op`, `den_freshRA_op`). No theorem relates `NomProp` to the
`iOwn` ownership in `IProp`.

## What it adds

### `Nominal/Lambda.lean` (core, mathlib-only) — the λ-calculus as a nominal set

Terms defined *nominally from the start*: raw terms carry the `FinPerm` action and
form a `NomSet`; quotienting by α-equivalence yields `Tm`, with an α-correct
binder.

- `Raw` / `atoms` / `fv`; `instance : NomSet Raw`.
- `AEq` — α-equivalence as a **generated congruence** (`refl`/`symm`/`trans` are
  constructors, so it is an equivalence relation by construction).
- `Tm := Raw / AEq`, `Tm.var` / `Tm.app` / `Tm.lam`; `instance : NomSet Tm`
  (support = `fv`, minimality via `aeq_of_fixes_fv`).
- `Tm.lam_rename` — **α-correctness of the binder**: `lam a t = lam b (swap a b • t)`
  for fresh `b`, as a property of the term.

`Nominal/LambdaAbs.lean` proves `Tm.lam a t = tmLam (abs a t)`: the binder factors
through name abstraction `NameAbs Tm`, which gives the fv-based α-rename
(`Tm.lam_rename_fresh`) and the some=any principle (`Tm.lam_some_any`).

### `NominalIris/*` (iris-lean layer, over `Atom`)

- **`Separation`** — assertions in iris-lean's classical BI `NomProp = HeapProp Unit`
  (the `ℕ`-indexed state reached via `Atom.val`): `worldProp` / `freshName`,
  `worldProp_sep`, `freshName_sep_ne`.
- **`Camera`** — the `DisjointLeibnizSet` name camera; the frame-preserving update
  `name_alloc` (`● S ~~> ● (S ∪ {a}) • ◯ {a}`); the `iOwn` / `|==>` layer `ownAuth` /
  `ownFresh` / `own_name_alloc` / `own_name_alloc_init` / `ownFresh_distinct`;
  `HasNameAlloc` and the `⊨auth` / `⊨fresh` notation.
- **`Den`** — `den`, a monoid morphism from the camera into `NomProp` (`den_op`,
  `den_valid_iff`, `den_freshRA`), with `den_freshRA_op`
  (`den (freshRA a • freshRA b) ⊣⊢ freshName a ∗ freshName b`),
  `concrete_sep_iff_camera_valid` and `freshName_sep_ne_via_camera`. The permutation
  action: `permState` on states and `permProp` on propositions, a `MulAction FinPerm
  NomProp`, preserving entailment in both directions (`permProp_entails_iff`), `∗`
  (`permProp_sep`), `emp` and pure propositions, with `permProp_worldProp`,
  `permProp_freshName`, `permProp_freshName_sep`, `freshName_sep_ne_perm` and
  `permProp_den_freshRA`.
- **`Lambda`** — `HasType`, the simply-typed judgment on `Tm`, whose `lam` rule requires
  the binder fresh for the context, with `HasType.freeVars_subset`. `CtxWF`, pairwise
  distinct binders, with `ctxWF_cons_iff` and `CtxWF.type_unique`. Ghost state: `ownCtx`
  (authoritative ownership of the context's set of binders), `abs_alloc` (allocation of
  a binder), `abs_alloc_wf` (a well-formed context has a well-formed extension) and
  `abs_alloc_hasType` (the allocation discharges the freshness premise of
  `HasType.lam`). `ownBinders` (one owned fragment per list entry), with
  `nFresh_sep_ownBinders`, `ownBinders_wf`, `ownCtx_ownBinders_wf`, `ownBinders_alloc`
  and `ownCtx_nFresh_mem`. `binders_distinct`, `alloc_and_bind` and
  `Tm.bound_not_free`, the last of which holds for every name without ghost state.

## Design notes

- **One framework.** Atoms/name-worlds/terms use nominal-lean's nominal-sets
  framework; the BI props are built over those atoms. `NomProp` is *not* itself a
  `NomSet`, since not every proposition is finitely supported. Its action `permProp`
  needs no support.
- **Reused components.** `NomProp = HeapProp Unit` is iris-lean's classical BI; this
  layer adds no BI instance. The name camera is iris-lean's `DisjointLeibnizSet`, the
  counterpart of Rocq's `gset_disj`.
- **Context ownership.** `ownCtx` owns a `Finset`, which forgets multiplicity, so it
  does not determine `CtxWF`. `CtxWF` comes from a hypothesis (`abs_alloc_wf`) or from
  the binder fragments (`ownBinders_wf`). `HasType` is not used in any ghost state:
  the only link is that allocation supplies the premise of its `lam` rule.
- **Step-indexing.** `Separation` and the action in `Den` use no `▷`/step-indexing;
  `Camera` and `Lambda` are in `IProp`, which is step-indexed.

## Dependencies / hygiene

- Adds `require iris` (the fork spitters/iris-catcrypt, `v4.35.0-catcrypt.1`) to the
  lakefile; used only by the `NominalIris` target. The core `Nominal` library stays
  mathlib-only.
- No `sorry`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Builds with `lake build NominalIris`.

## Follow-ups

- The `И`-quantifier over name-worlds, alongside the some=any principle for the
  binder (`Tm.lam_some_any`) already in `LambdaAbs`.
- Equivariance of `HasType`.
- Subject reduction and Church–Rosser on `Tm`: substitution via the nominal
  recursor `NameAbs.lift` (α handled by construction through `tmLam`).
- A semantic type-safety proof (logical relations) over iris-lean's WP.
