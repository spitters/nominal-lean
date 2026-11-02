/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import NominalIris.Camera
public import Nominal.Lambda

/-!
# Binding the nominal λ-calculus with name-allocation ghost state

The nominal λ-terms `Tm` (α-quotiented, `Nominal.Lambda`), a simply-typed judgment on them, and
the name-allocation ghost state (`NominalIris.Camera`), over the one type `Atom`.

* `HasType` — the judgment `Γ ⊢ t : T`, whose `lam` rule requires the binder fresh for `Γ`;
  `HasType.freeVars_subset` — the free variables of a typable term are bound by its context.
* `CtxWF` — pairwise distinct binders, `(Γ.map Prod.fst).Nodup`; `CtxWF.type_unique`.
* `ownCtx` — authoritative ownership of the set of binders of a context. This set forgets
  multiplicity, so `ownCtx` alone does not determine `CtxWF`.
* `abs_alloc` — allocate a binder fresh for `Γ` by the frame-preserving update `name_alloc`;
  `abs_alloc_wf` — the extension of a well-formed context is well-formed;
  `abs_alloc_hasType` — the allocation discharges the freshness premise of `HasType.lam`.
* `ownBinders` — one owned fragment per list entry; `ownBinders_wf` — this ownership gives
  `CtxWF`; `ownBinders_alloc` — allocation extends the allocator and the fragments together;
  `ownCtx_nFresh_mem` — an owned fragment lies in the allocator's set.
* `binders_distinct` — two owned fragments carry distinct names.
* `Tm.bound_not_free` — the bound name of a nominal abstraction is not free in it, for every
  name; `alloc_and_bind` pairs this fact with an allocation.
-/

set_option autoImplicit false

@[expose] public section

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

/-- The free variables of a variable. -/
theorem Tm.freeVars_var (a : Atom) : Tm.freeVars (Tm.var a) = {a} := by
  simp [CatCrypt.Nominal.Lambda.Tm.var]

/-- The free variables of an application: the union of those of its parts. -/
theorem Tm.freeVars_app (s t : Tm) :
    Tm.freeVars (Tm.app s t) = Tm.freeVars s ∪ Tm.freeVars t := by
  induction s using CatCrypt.Nominal.Lambda.Tm.ind with
  | _ r =>
    induction t using CatCrypt.Nominal.Lambda.Tm.ind with
    | _ r' => exact CatCrypt.Nominal.Lambda.fv_app r r'

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

/-! ## The typing judgment and well-formed contexts -/

/-- The simply-typed judgment `Γ ⊢ t : T` on α-quotiented terms. The `lam` rule requires the
bound name fresh for the context. -/
inductive HasType : Ctx → Tm → Ty → Prop where
  | var {Γ : Ctx} {a : Atom} {T : Ty} : (a, T) ∈ Γ → HasType Γ (Tm.var a) T
  | app {Γ : Ctx} {t u : Tm} {S T : Ty} :
      HasType Γ t (.arr S T) → HasType Γ u S → HasType Γ (Tm.app t u) T
  | lam {Γ : Ctx} {a : Atom} {t : Tm} {S T : Ty} :
      a ∉ ctxDom Γ → HasType ((a, S) :: Γ) t T → HasType Γ (Tm.lam a t) (.arr S T)

/-- A context is well-formed when its binders are pairwise distinct. -/
def CtxWF (Γ : Ctx) : Prop := (Γ.map Prod.fst).Nodup

theorem ctxWF_nil : CtxWF [] := List.nodup_nil

/-- Extending a context by a binder is well-formed iff the binder is fresh and the context is
well-formed. -/
theorem ctxWF_cons_iff {a : Atom} {S : Ty} {Γ : Ctx} :
    CtxWF ((a, S) :: Γ) ↔ a ∉ ctxDom Γ ∧ CtxWF Γ := by
  simp [CtxWF, ctxDom]

/-- A well-formed context assigns one type to each binder. -/
theorem CtxWF.type_unique {Γ : Ctx} (h : CtxWF Γ) {a : Atom} {S T : Ty}
    (hS : (a, S) ∈ Γ) (hT : (a, T) ∈ Γ) : S = T := by
  have := List.inj_on_of_nodup_map h hS hT rfl
  simpa using this

/-- The free variables of a typable term are bound by its context. -/
theorem HasType.freeVars_subset {Γ : Ctx} {t : Tm} {T : Ty} (h : HasType Γ t T) :
    Tm.freeVars t ⊆ ctxDom Γ := by
  induction h with
  | @var Γ a T hmem =>
    rw [Tm.freeVars_var, Finset.singleton_subset_iff, ctxDom, List.mem_toFinset]
    exact List.mem_map_of_mem (f := Prod.fst) hmem
  | app _ _ ihs iht => exact Tm.freeVars_app _ _ ▸ Finset.union_subset ihs iht
  | lam _ _ ih =>
    rw [Tm.freeVars_lam, ctxDom_cons] at *
    exact fun x hx => by grind

section Binding

variable {GF : BundledGFunctors}

/-- Authoritative ownership of the set of binders of a context, in the name allocator. -/
def ownCtx (γ : GName) [HasNameAlloc γ GF] (Γ : Ctx) : IProp GF :=
  nAuth γ (NameSet.ofFinset (ctxDom Γ))

/-- **Allocation of a binder.** Allocate a name fresh for the context, obtaining `a ∉ ctxDom Γ`,
ownership of its fragment, and the allocator of the extended context. -/
theorem abs_alloc (γ : GName) [HasNameAlloc γ GF] (Γ : Ctx) (S : Ty) :
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
  · ipureintro; exact ha
  · isplitl [Hf]
    · iexact Hf
    · iexact Hauth

/-- Two owned fragments carry distinct names. `ownBinders_wf` is its form for a context. -/
theorem binders_distinct (γ : GName) [HasNameAlloc γ GF] (a b : Atom) :
    (nFresh γ a ∗ nFresh γ b : IProp GF) ⊢ ⌜a ≠ b⌝ := by
  unfold nFresh
  exact ownFresh_distinct γ a b

/-- **Allocate a binder and form an abstraction.** From the context allocator, allocate a name,
own its fragment, and state that it is not free in `Tm.lam a t`. That conjunct holds for every
name (`Tm.bound_not_free`) and does not depend on the ghost state. -/
theorem alloc_and_bind (γ : GName) [HasNameAlloc γ GF] (Γ : Ctx) (S : Ty) (t : Tm) :
    ownCtx γ Γ ⊢
      |==> ∃ a : Atom, nFresh γ a ∗ ⌜a ∉ Tm.freeVars (Tm.lam a t)⌝ ∗ ownCtx γ ((a, S) :: Γ) := by
  refine (abs_alloc γ Γ S).trans (BIUpdate.mono ?_)
  iintro ⟨%a, _, Hf, Hc⟩
  iexists a
  isplitl [Hf]
  · iexact Hf
  · isplit
    · ipureintro; exact Tm.bound_not_free a t
    · iexact Hc

/-! ## Name allocation discharges the typing rule's freshness condition -/

/-- From a well-formed context, name allocation gives a binder whose extension of the context
is well-formed. -/
theorem abs_alloc_wf (γ : GName) [HasNameAlloc γ GF] {Γ : Ctx} (hΓ : CtxWF Γ) (S : Ty) :
    ownCtx γ Γ ⊢ |==> ∃ a : Atom, ⌜CtxWF ((a, S) :: Γ)⌝ ∗ nFresh γ a ∗ ownCtx γ ((a, S) :: Γ) := by
  refine (abs_alloc γ Γ S).trans (BIUpdate.mono ?_)
  iintro ⟨%a, %ha, Hf, Hc⟩
  iexists a
  isplit
  · ipureintro; exact ctxWF_cons_iff.mpr ⟨ha, hΓ⟩
  · isplitl [Hf]
    · iexact Hf
    · iexact Hc

/-- Name allocation discharges the freshness premise of `HasType.lam`: given a body typable
under every fresh extension of `Γ`, the allocated binder forms a typed abstraction. -/
theorem abs_alloc_hasType (γ : GName) [HasNameAlloc γ GF] (Γ : Ctx) (S T : Ty) (t : Atom → Tm)
    (ht : ∀ a, a ∉ ctxDom Γ → HasType ((a, S) :: Γ) (t a) T) :
    ownCtx γ Γ ⊢ |==> ∃ a : Atom,
      ⌜HasType Γ (Tm.lam a (t a)) (.arr S T)⌝ ∗ nFresh γ a ∗ ownCtx γ ((a, S) :: Γ) := by
  refine (abs_alloc γ Γ S).trans (BIUpdate.mono ?_)
  iintro ⟨%a, %ha, Hf, Hc⟩
  iexists a
  isplit
  · ipureintro; exact .lam ha (ht a ha)
  · isplitl [Hf]
    · iexact Hf
    · iexact Hc

/-! ## Binder fragments: well-formedness from ownership -/

/-- Separating ownership of the fresh-name fragment of each binder of `Γ`, one per list entry. -/
def ownBinders (γ : GName) [HasNameAlloc γ GF] : Ctx → IProp GF
  | [] => iprop(emp)
  | (a, _) :: Γ => iprop(nFresh γ a ∗ ownBinders γ Γ)

/-- An owned name is fresh for the context whose binder fragments are owned beside it. -/
theorem nFresh_sep_ownBinders (γ : GName) [HasNameAlloc γ GF] (a : Atom) (Γ : Ctx) :
    (nFresh γ a ∗ ownBinders γ Γ : IProp GF) ⊢ ⌜a ∉ ctxDom Γ⌝ := by
  induction Γ with
  | nil => exact BI.pure_intro (by simp [ctxDom])
  | cons p Γ ih =>
    obtain ⟨b, S⟩ := p
    rw [ownBinders]
    have hne : (nFresh γ a ∗ nFresh γ b ∗ ownBinders γ Γ : IProp GF) ⊢ ⌜a ≠ b⌝ :=
      (sep_mono_right sep_elim_left).trans (binders_distinct γ a b)
    have hfr : (nFresh γ a ∗ nFresh γ b ∗ ownBinders γ Γ : IProp GF) ⊢ ⌜a ∉ ctxDom Γ⌝ :=
      (sep_mono_right sep_elim_right).trans ih
    refine (and_intro hne hfr).trans (pure_and.1.trans (pure_mono ?_))
    exact fun ⟨h₁, h₂⟩ => by simp [h₁, h₂]

/-- Owning a fragment for each list entry forces the binders of `Γ` pairwise distinct. -/
theorem ownBinders_wf (γ : GName) [HasNameAlloc γ GF] (Γ : Ctx) :
    (ownBinders γ Γ : IProp GF) ⊢ ⌜CtxWF Γ⌝ := by
  induction Γ with
  | nil => exact BI.pure_intro ctxWF_nil
  | cons p Γ ih =>
    obtain ⟨a, S⟩ := p
    rw [ownBinders]
    exact (and_intro (nFresh_sep_ownBinders γ a Γ) (sep_elim_right.trans ih)).trans
      (pure_and.1.trans (pure_mono ctxWF_cons_iff.mpr))

/-- A context owned as allocator and binder fragments has pairwise distinct binders. The
fragments carry this fact: the allocator's set forgets multiplicity. -/
theorem ownCtx_ownBinders_wf (γ : GName) [HasNameAlloc γ GF] (Γ : Ctx) :
    (ownCtx γ Γ ∗ ownBinders γ Γ : IProp GF) ⊢ ⌜CtxWF Γ⌝ :=
  sep_elim_right.trans (ownBinders_wf γ Γ)

/-- A name whose fragment is owned beside the context allocator lies in the context's domain. -/
theorem ownCtx_nFresh_mem (γ : GName) [HasNameAlloc γ GF] (Γ : Ctx) (a : Atom) :
    (ownCtx γ Γ ∗ nFresh γ a : IProp GF) ⊢ ⌜a ∈ ctxDom Γ⌝ := by
  unfold ownCtx nAuth nFresh ownAuth ownFresh
  refine iOwn_cmraValid_op.trans (internalCmraValid_discrete.1.trans (pure_mono fun hv => ?_))
  have hinc := (Auth.auth_both_valid_discrete.mp hv).1
  have hsub := DisjointLeibnizSet.included_iff_subset.mp hinc
  exact hsub a (by simp)

/-- Allocation preserves the pair of the allocator and the binder fragments. By
`ownBinders_wf` the extended context of the result is well-formed. -/
theorem ownBinders_alloc (γ : GName) [HasNameAlloc γ GF] (Γ : Ctx) (S : Ty) :
    (ownCtx γ Γ ∗ ownBinders γ Γ : IProp GF) ⊢
      |==> ∃ a : Atom, ⌜a ∉ ctxDom Γ⌝ ∗ ownCtx γ ((a, S) :: Γ) ∗ ownBinders γ ((a, S) :: Γ) := by
  iintro ⟨Hc, Hb⟩
  imod abs_alloc γ Γ S $$ Hc with ⟨%a, %ha, Hf, Hc⟩
  imodintro
  iexists a
  isplit
  · ipureintro; exact ha
  · isplitl [Hc]
    · iexact Hc
    · rw [ownBinders]
      isplitl [Hf]
      · iexact Hf
      · iexact Hb

end Binding

end NominalIris
