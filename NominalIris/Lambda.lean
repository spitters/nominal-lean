/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/
import NominalIris.Camera
import Nominal.Lambda

set_option autoImplicit false

/-!
# Binding the nominal λ-calculus with name-allocation ghost state

The nominal λ-terms `Tm` (α-quotiented, `Nominal.Lambda`) and the name-allocation
ghost state (`NominalIris.Camera`) share the one `Atom` framework, so binding can
be expressed *in Iris*: a typing context is a ghost **name allocator**, the
`(Abs)` rule allocates its bound variable as the `name_alloc` view-shift, and the
allocated fresh name binds a genuine α-correct nominal abstraction `Tm.lam`.

* `ownCtx` / `abs_alloc` / `binders_distinct` — the binding model over `Atom`.
* `Tm.bound_not_free` — the bound name of a nominal abstraction is not free in it.
* `alloc_and_bind` — allocate a fresh binder and form a well-scoped nominal
  abstraction, under the basic update.
-/

namespace NominalIris

open CatCrypt.Nominal (Atom)
open CatCrypt.Nominal.Lambda (Tm)
open Iris Iris.BI CMRA COFE

/-! ## Nominal terms: the bound name is fresh for the abstraction -/

/-- Free variables of a nominal abstraction: the body's, minus the binder. -/
theorem Tm.freeVars_lam (a : Atom) (t : Tm) :
    Tm.freeVars (Tm.lam a t) = Tm.freeVars t \ {a} := by
  induction t using CatCrypt.Nominal.Lambda.Tm.ind with
  | _ r => simp [CatCrypt.Nominal.Lambda.Tm.lam_mk]

/-- **The bound name is not free in the abstraction** — well-scopedness of a
nominal binder, holding as a property of the term. -/
theorem Tm.bound_not_free (a : Atom) (t : Tm) : a ∉ Tm.freeVars (Tm.lam a t) := by
  rw [Tm.freeVars_lam]; simp

/-! ## Simple types and the context allocator -/

/-- Simple types. -/
inductive Ty where
  | base : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq

/-- A typing context. -/
abbrev Ctx : Type := List (Atom × Ty)

/-- The atoms a context binds. -/
def ctxDom (Γ : Ctx) : Finset Atom := (Γ.map Prod.fst).toFinset

@[simp] theorem ctxDom_cons (a : Atom) (T : Ty) (Γ : Ctx) :
    ctxDom ((a, T) :: Γ) = insert a (ctxDom Γ) := by simp [ctxDom]

theorem nameSet_eq {s t : NameSet} (h : s.toFinset = t.toFinset) : s = t := by
  cases s; cases t; exact congrArg _ h

theorem ctxNS_cons (a : Atom) (T : Ty) (Γ : Ctx) :
    NameSet.ofFinset (ctxDom ((a, T) :: Γ)) = NameSet.ofFinset (ctxDom Γ) ∪ {a} := by
  apply nameSet_eq
  simp only [NameSet.toFinset_union, NameSet.toFinset_singleton, ctxDom_cons]
  ext x
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, or_comm]

section Binding

variable {Fr : Type _} [UFraction Fr] {GF : BundledGFunctors}

/-- A typing context realised as a ghost name allocator. -/
def ownCtx (γ : GName) [HasNameAlloc γ GF Fr] (Γ : Ctx) : IProp GF :=
  nAuth γ (NameSet.ofFinset (ctxDom Γ))

/-- **The `(Abs)` rule as fresh-name allocation.** Allocate a fresh binder for
the context, obtaining `a # Γ`, ownership of it, and the extended context. -/
theorem abs_alloc (γ : GName) [HasNameAlloc γ GF Fr] (Γ : Ctx) (S : Ty) :
    ownCtx γ Γ ⊢ |==> ∃ a : Atom, ⌜a ∉ ctxDom Γ⌝ ∗ nFresh γ a ∗ ownCtx γ ((a, S) :: Γ) := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ ctxDom Γ := ⟨Atom.fresh (ctxDom Γ), Atom.fresh_not_mem _⟩
  unfold ownCtx nAuth nFresh
  iintro H
  imod own_name_alloc γ (S := NameSet.ofFinset (ctxDom Γ)) (a := a) (by simpa using ha) $$ H
    with ⟨Hauth, Hf⟩
  imodintro
  iexists a
  rw [ctxNS_cons]
  isplit
  · ipure_intro; exact ha
  · isplitl [Hf]
    · iexact Hf
    · iexact Hauth

/-- **Context well-formedness is separation**: two owned binder names are distinct. -/
theorem binders_distinct (γ : GName) [HasNameAlloc γ GF Fr] (a b : Atom) :
    (nFresh γ a ∗ nFresh γ b : IProp GF) ⊢ ⌜a ≠ b⌝ := by
  unfold nFresh
  exact ownFresh_distinct γ a b

/-- **Allocate a fresh binder and bind a nominal term.** From the context
allocator, allocate `a # Γ`, obtain ownership of it, and form the α-correct
nominal abstraction `Tm.lam a t`, whose bound name is provably fresh for it. -/
theorem alloc_and_bind (γ : GName) [HasNameAlloc γ GF Fr] (Γ : Ctx) (S : Ty) (t : Tm) :
    ownCtx γ Γ ⊢
      |==> ∃ a : Atom, nFresh γ a ∗ ⌜a ∉ Tm.freeVars (Tm.lam a t)⌝ ∗ ownCtx γ ((a, S) :: Γ) := by
  refine (abs_alloc γ Γ S).trans (BIUpdate.mono ?_)
  iintro ⟨%a, _, Hf, Hc⟩
  iexists a
  isplitl [Hf]
  · iexact Hf
  · isplit
    · ipure_intro; exact Tm.bound_not_free a t
    · iexact Hc

end Binding

end NominalIris
