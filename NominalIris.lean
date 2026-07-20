/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/
import NominalIris.Separation
import NominalIris.Camera
import NominalIris.Den
import NominalIris.Lambda

/-!
# `NominalIris` — nominal separation and binding in Iris

The Iris/BI layer of the nominal development, over nominal-lean's `Atom` (so it
shares the `Atom` / `FinPerm` / `NomSet` framework with the nominal λ-terms in
`Nominal.Lambda`). Depends on iris-lean; the core `Nominal` library stays
mathlib-only.

* `NominalIris.Separation` — nominal separation as a model of (classical,
  non-affine) BI: `NomProp` (iris-lean's classical heap BI, the `ℕ`-indexed
  state reached via `Atom.val`), `worldProp` / `freshName`, and the headline
  `freshName_sep_ne : freshName a ∗ freshName b ⊢ ⌜a ≠ b⌝`.
* `NominalIris.Camera` — the `DisjointLeibnizSet` name camera, the `Auth`
  allocation view-shift `name_alloc`, and the `iOwn` / `|==>` ghost-state layer
  (`ownAuth` / `ownFresh` / `own_name_alloc` / `ownFresh_distinct`) with a
  points-to notation.
* `NominalIris.Den` — the `den` monoid morphism from the camera into the concrete
  BI, proving the two readings agree (`concrete_sep_iff_camera_valid`).
* `NominalIris.Lambda` — binding the nominal λ-terms `Nominal.Lambda.Tm` with the
  name-allocation ghost state: `ownCtx` (context as ghost allocator), `abs_alloc`
  ((Abs) as a `name_alloc` view-shift), `binders_distinct` (well-formedness as
  separation), and `alloc_and_bind` (allocate a fresh binder and form the
  α-correct abstraction `Tm.lam`).

Everything is over one framework: atoms, name-worlds, and terms live in
nominal-lean's nominal-sets framework; the BI propositions are built over those
atoms (`NomProp` is not itself a nominal set — not every proposition is finitely
supported).
-/
