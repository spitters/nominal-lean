# Nominal separation and binding in Iris

## Summary

This PR adds an Iris/BI layer on top of nominal-lean: nominal separation as a
model of bunched implications, a name-allocation ghost state, and the
simply-typed λ-calculus whose binding is expressed as that ghost state, built on
an α-quotient nominal term type. Atoms, name-worlds, and terms live in
nominal-lean's `Atom` / `FinPerm` / `NomSet`; the Iris layer (`NominalIris.*`) is
built over those atoms.

The headline law is the nominal analogue of `ℓ₁ ↦ ∗ ℓ₂ ↦ ⊢ ℓ₁ ≠ ℓ₂`:

```lean
theorem freshName_sep_ne (a b : Atom) :
    (freshName a ∗ freshName b : NomProp) ⊢ iprop(⌜a ≠ b⌝)
```

and its ghost-state image is that two owned fresh names are distinct
(`ownFresh_distinct`), which is exactly the well-formedness (distinct binders) of
a typing context.

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

- **`Separation`** — nominal separation as classical BI: `NomProp = HeapProp Unit`
  (the `ℕ`-indexed state reached via `Atom.val`), `worldProp` / `freshName`,
  `worldProp_sep`, `freshName_sep_ne`.
- **`Camera`** — the `DisjointLeibnizSet` name camera; `name_alloc`
  (`● S ~~> ● (S ∪ {a}) • ◯ {a}`); the `iOwn` / `|==>` layer `ownAuth` /
  `ownFresh` / `own_name_alloc` / `own_name_alloc_init` / `ownFresh_distinct`;
  `HasNameAlloc` + points-to notation.
- **`Den`** — `den`, a monoid morphism from the camera into the concrete BI,
  proving the two readings agree (`den_op`, `den_valid_iff`,
  `concrete_sep_iff_camera_valid`, `freshName_sep_ne_via_camera`).
- **`Lambda`** — binding the nominal `Tm` with the ghost state: `ownCtx` (context
  as ghost allocator), `abs_alloc` ((Abs) as a `name_alloc` view-shift),
  `binders_distinct` (well-formedness as separation), and `alloc_and_bind` —
  allocate a fresh binder and form the α-correct abstraction `Tm.lam a t`, bound
  name provably fresh (`Tm.bound_not_free`).

## Design notes

- **One framework.** Atoms/name-worlds/terms use nominal-lean's nominal-sets
  framework; the BI props are built over those atoms. `NomProp` is *not* itself a
  `NomSet` — not every proposition is finitely supported — so permutation /
  equivariance for the nominal objects comes from `NomSet` / `FinPerm`, not a
  bespoke action on `NomProp`.
- **Reused components.** `NomProp = HeapProp Unit` is iris-lean's classical BI,
  so `∗` is disjoint name-support splitting. The name camera is iris-lean's
  `DisjointLeibnizSet` (the `gset`/`copset` RA).
- **Classical fragment.** Name resources are flat and first-order, so the
  development uses no `▷`/OFE/step-indexing, and `name_alloc` is a discrete ghost
  update.

## Dependencies / hygiene

- Adds `require iris` (iris-lean, `v4.30.0`) to the lakefile; used only by the
  `NominalIris` target. The core `Nominal` library stays mathlib-only.
- No `sorry`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Builds with `lake build NominalIris`.

## Follow-ups

- The `И`-quantifier over name-worlds, alongside the some=any principle for the
  binder (`Tm.lam_some_any`) already in `LambdaAbs`.
- Subject reduction and Church–Rosser on `Tm`: substitution via the nominal
  recursor `NameAbs.lift` (α handled by construction through `tmLam`).
- A semantic type-safety proof (logical relations) over iris-lean's WP.
