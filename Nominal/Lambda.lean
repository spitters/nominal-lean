/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/
import Nominal.NameAbstraction
import Nominal.Fresh

set_option autoImplicit false

/-!
# The λ-calculus as a nominal set

The λ-calculus with terms defined *nominally from the start*, over the
`Atom` / `FinPerm` / `NomSet` framework. Raw terms carry the `FinPerm` action and
form a `NomSet`; quotienting by α-equivalence yields `Tm`, the genuine nominal
term type. Changing the bound name of `lam` to any fresh atom leaves the term
equal (`Tm.lam_rename`) — an equality of terms, not a separate α-relation.

## Main definitions

* `Raw`, `atoms`, `fv` — raw terms, their atoms, and free variables.
* `AEq` — α-equivalence as a generated congruence (`refl`/`symm`/`trans` are
  constructors, so it is an equivalence relation by construction).
* `Tm := Raw / AEq` — nominal λ-terms; `Tm.var` / `Tm.app` / `Tm.lam`.

## Main results

* `instance : NomSet Raw` — raw terms as a nominal set (support = all atoms).
* `instance : NomSet Tm` — nominal λ-terms as a nominal set (support = `fv`),
  whose support-minimality is `aeq_of_fixes_fv`.
* `Tm.lam_rename` — α-correctness of the binder.

## References

* A. M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, CUP 2013.
-/

namespace CatCrypt.Nominal.Lambda

open CatCrypt.Nominal

/-! ## Raw λ-terms and the permutation action -/

/-- Raw (pre-α) λ-terms over atoms. -/
inductive Raw where
  | var : Atom → Raw
  | app : Raw → Raw → Raw
  | lam : Atom → Raw → Raw
  deriving DecidableEq

/-- The `FinPerm` action on raw terms: rename every atom (free and bound). -/
def rawAct (π : FinPerm) : Raw → Raw
  | .var a   => .var (π a)
  | .app s t => .app (rawAct π s) (rawAct π t)
  | .lam a t => .lam (π a) (rawAct π t)

theorem rawAct_one (t : Raw) : rawAct 1 t = t := by
  induction t with
  | var a => simp [rawAct]
  | app s t ihs iht => simp [rawAct, ihs, iht]
  | lam a t iht => simp [rawAct, iht]

theorem rawAct_mul (π₁ π₂ : FinPerm) (t : Raw) :
    rawAct (π₁ * π₂) t = rawAct π₁ (rawAct π₂ t) := by
  induction t with
  | var a => simp [rawAct]
  | app s t ihs iht => simp [rawAct, ihs, iht]
  | lam a t iht => simp [rawAct, iht]

instance : MulAction FinPerm Raw where
  smul := rawAct
  one_smul := rawAct_one
  mul_smul := rawAct_mul

@[simp] theorem smul_var (π : FinPerm) (a : Atom) : π • Raw.var a = Raw.var (π a) := rfl
@[simp] theorem smul_app (π : FinPerm) (s t : Raw) :
    π • Raw.app s t = Raw.app (π • s) (π • t) := rfl
@[simp] theorem smul_lam (π : FinPerm) (a : Atom) (t : Raw) :
    π • Raw.lam a t = Raw.lam (π a) (π • t) := rfl

/-! ## Atoms of a term and the `NomSet` structure -/

/-- Every atom occurring in a term (free or bound) — the support of the *raw*
term (raw terms are not yet α-quotiented, so bound names count). -/
def atoms : Raw → Finset Atom
  | .var a   => {a}
  | .app s t => atoms s ∪ atoms t
  | .lam a t => insert a (atoms t)

@[simp] theorem atoms_var (a : Atom) : atoms (.var a) = {a} := rfl
@[simp] theorem atoms_app (s t : Raw) : atoms (.app s t) = atoms s ∪ atoms t := rfl
@[simp] theorem atoms_lam (a : Atom) (t : Raw) : atoms (.lam a t) = insert a (atoms t) := rfl

theorem atoms_smul (π : FinPerm) (t : Raw) : atoms (π • t) = (atoms t).image (π ·) := by
  induction t with
  | var a => simp
  | app s t ihs iht => simp [ihs, iht, Finset.image_union]
  | lam a t iht => simp [iht, Finset.image_insert]

/-- If a permutation fixes every atom of `t`, it fixes `t`. -/
theorem smul_eq_of_atoms_fixed {π : FinPerm} {t : Raw}
    (h : ∀ a ∈ atoms t, π a = a) : π • t = t := by
  induction t with
  | var a => simp only [smul_var, h a (by simp)]
  | app s t ihs iht =>
    simp only [smul_app]
    rw [ihs (fun a ha => h a (by simp [ha])), iht (fun a ha => h a (by simp [ha]))]
  | lam a t iht =>
    simp only [smul_lam, h a (by simp)]
    rw [iht (fun b hb => h b (by simp [hb]))]

instance : NomSet Raw where
  supp := atoms
  supp_supports := fun _ _ h => smul_eq_of_atoms_fixed h
  supp_equivariant := fun t π => atoms_smul π t

@[simp] theorem supp_raw (t : Raw) : NomSet.supp t = atoms t := rfl

/-! ## Free variables -/

/-- The free variables of a term (`lam` binds). -/
def fv : Raw → Finset Atom
  | .var a   => {a}
  | .app s t => fv s ∪ fv t
  | .lam a t => fv t \ {a}

@[simp] theorem fv_var (a : Atom) : fv (.var a) = {a} := rfl
@[simp] theorem fv_app (s t : Raw) : fv (.app s t) = fv s ∪ fv t := rfl
@[simp] theorem fv_lam (a : Atom) (t : Raw) : fv (.lam a t) = fv t \ {a} := rfl

theorem fv_subset_atoms (t : Raw) : fv t ⊆ atoms t := by
  induction t with
  | var a => simp
  | app s t ihs iht => exact Finset.union_subset_union ihs iht
  | lam a t iht => exact (Finset.sdiff_subset).trans (iht.trans (Finset.subset_insert _ _))

theorem fv_smul (π : FinPerm) (t : Raw) : fv (π • t) = (fv t).image (π ·) := by
  induction t with
  | var a => simp
  | app s t ihs iht => simp [ihs, iht, Finset.image_union]
  | lam a t iht =>
    simp only [smul_lam, fv_lam, iht]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hne⟩
      exact ⟨y, ⟨hy, fun h => hne (by rw [h])⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hya⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, fun h => hya (π.val.injective h)⟩

/-! ## α-equivalence (generated congruence) and the quotient

`AEq` is the least congruence identifying `lam a t` with `lam b (swap a b • t)`
for a fresh `b`. Taking `refl`/`symm`/`trans` as constructors makes it an
equivalence relation *by construction* — no hand proof of α-transitivity. -/

/-- α-equivalence of raw terms. -/
inductive AEq : Raw → Raw → Prop
  | rfl (t : Raw) : AEq t t
  | symm {s t} : AEq s t → AEq t s
  | trans {s t u} : AEq s t → AEq t u → AEq s u
  | app {s s' t t'} : AEq s s' → AEq t t' → AEq (.app s t) (.app s' t')
  | lam {a s t} : AEq s t → AEq (.lam a s) (.lam a t)
  | rename (a b : Atom) (t : Raw) (h : b ∉ atoms t) :
      AEq (.lam a t) (.lam b (FinPerm.swap a b • t))

theorem AEq.equivalence : Equivalence AEq := ⟨AEq.rfl, AEq.symm, AEq.trans⟩

/-- α-equivalence is equivariant. -/
theorem aeq_smul (π : FinPerm) {s t : Raw} (h : AEq s t) : AEq (π • s) (π • t) := by
  induction h with
  | rfl t => exact .rfl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ ih => exact .lam ih
  | rename a b t hb =>
    simp only [smul_lam]
    have hb' : π b ∉ atoms (π • t) := by
      rw [atoms_smul]
      intro hc
      obtain ⟨c, hcm, hce⟩ := Finset.mem_image.mp hc
      exact hb (π.val.injective hce ▸ hcm)
    have hconj := swap_smul_conj π a b t
    exact hconj ▸ AEq.rename (π a) (π b) (π • t) hb'

/-- α-equivalent terms have the same free variables. -/
theorem aeq_fv {s t : Raw} (h : AEq s t) : fv s = fv t := by
  induction h with
  | rfl t => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => simp only [fv_app, ih1, ih2]
  | lam _ ih => simp only [fv_lam, ih]
  | rename a b t hb =>
    have hbfv : b ∉ fv t := fun hc => hb (fv_subset_atoms t hc)
    simp only [fv_lam, fv_smul]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨x, hx, FinPerm.swap_apply_of_ne_of_ne hxa (fun h => hbfv (h ▸ hx))⟩,
        fun hxb => hbfv (hxb ▸ hx)⟩
    · rintro ⟨⟨y, hy, hyx⟩, hxb⟩
      rcases eq_or_ne y a with rfl | hya
      · exact absurd (by rw [← hyx, FinPerm.swap_apply_left]) hxb
      · rcases eq_or_ne y b with rfl | hyb
        · exact absurd hy hbfv
        · rw [FinPerm.swap_apply_of_ne_of_ne hya hyb] at hyx
          exact ⟨hyx ▸ hy, fun hxa => hya (hyx ▸ hxa)⟩

/-! ## The nominal term type `Tm := Raw / α` -/

/-- The α-equivalence setoid. -/
def aeqSetoid : Setoid Raw := ⟨AEq, AEq.equivalence⟩

/-- **Nominal λ-terms**: raw terms up to α-equivalence. -/
def Tm : Type := Quotient aeqSetoid

/-- The class of a raw term. -/
def Tm.mk (t : Raw) : Tm := Quotient.mk aeqSetoid t

theorem Tm.mk_eq {s t : Raw} (h : AEq s t) : Tm.mk s = Tm.mk t := Quotient.sound h

@[elab_as_elim]
theorem Tm.ind {motive : Tm → Prop} (h : ∀ t : Raw, motive (Tm.mk t)) (q : Tm) : motive q :=
  Quotient.ind h q

/-- The permutation action descends to the quotient. -/
instance : MulAction FinPerm Tm where
  smul π := Quotient.lift (fun t => Tm.mk (π • t)) fun _ _ h => Tm.mk_eq (aeq_smul π h)
  one_smul := Tm.ind fun t => Tm.mk_eq (by rw [one_smul]; exact AEq.rfl t)
  mul_smul π₁ π₂ := Tm.ind fun t => Tm.mk_eq (by rw [mul_smul]; exact AEq.rfl _)

@[simp] theorem Tm.smul_mk (π : FinPerm) (t : Raw) : π • Tm.mk t = Tm.mk (π • t) := rfl

/-- Free variables, descended to the quotient (α-invariant). -/
def Tm.freeVars : Tm → Finset Atom := Quotient.lift fv fun _ _ h => aeq_fv h

@[simp] theorem Tm.freeVars_mk (t : Raw) : Tm.freeVars (Tm.mk t) = fv t := rfl

/-! ### Constructors on `Tm`, and α-correctness of `lam` -/

/-- Variable. -/
def Tm.var (a : Atom) : Tm := Tm.mk (.var a)

/-- Application. -/
def Tm.app : Tm → Tm → Tm :=
  Quotient.lift₂ (fun s t => Tm.mk (.app s t))
    fun _ _ _ _ h₁ h₂ => Tm.mk_eq (AEq.app h₁ h₂)

/-- Abstraction (binding). -/
def Tm.lam (a : Atom) : Tm → Tm :=
  Quotient.lift (fun t => Tm.mk (.lam a t)) fun _ _ h => Tm.mk_eq (AEq.lam h)

@[simp] theorem Tm.lam_mk (a : Atom) (t : Raw) : Tm.lam a (Tm.mk t) = Tm.mk (.lam a t) := rfl

/-- **α-correctness of `lam`**: `lam a t = lam b (swap a b • t)` for fresh `b`,
an equality of terms — the defining property of a nominal binder. -/
theorem Tm.lam_rename (a b : Atom) (t : Raw) (h : b ∉ atoms t) :
    Tm.lam a (Tm.mk t) = Tm.lam b (Tm.mk (FinPerm.swap a b • t)) :=
  Tm.mk_eq (AEq.rename a b t h)

/-! ### Support minimality: `Tm` is a nominal set with `supp = fv`

The nontrivial half: a permutation fixing the *free* variables of a term acts
α-trivially on it. -/

/-- A permutation fixing every free variable of `t` fixes `t` up to α. -/
theorem aeq_of_fixes_fv : ∀ {t : Raw} {π : FinPerm}, (∀ a ∈ fv t, π a = a) → AEq (π • t) t := by
  intro t
  induction t with
  | var a =>
    intro π h; simp only [smul_var, h a (by simp)]; exact AEq.rfl _
  | app s t ihs iht =>
    intro π h
    simp only [smul_app]
    exact AEq.app (ihs fun a ha => h a (by simp [ha])) (iht fun a ha => h a (by simp [ha]))
  | lam a s ih =>
    intro π h
    simp only [smul_lam]
    set c := Atom.fresh (insert a (insert (π a) (atoms s ∪ atoms (π • s)))) with hcdef
    have hcmem := Atom.fresh_not_mem (insert a (insert (π a) (atoms s ∪ atoms (π • s))))
    rw [← hcdef] at hcmem
    have hca : c ≠ a := fun he => hcmem (by rw [he]; exact Finset.mem_insert_self _ _)
    have hcpa : c ≠ π a := fun he =>
      hcmem (by rw [he]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hcs : c ∉ atoms s := fun hc =>
      hcmem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hc)))
    have hcps : c ∉ atoms (π • s) := fun hc =>
      hcmem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hc)))
    have e1 : AEq (Raw.lam a s) (Raw.lam c (FinPerm.swap a c • s)) := AEq.rename a c s hcs
    have e2 : AEq (Raw.lam (π a) (π • s)) (Raw.lam c (FinPerm.swap (π a) c • (π • s))) :=
      AEq.rename (π a) c (π • s) hcps
    refine e2.trans (AEq.trans ?_ e1.symm)
    apply AEq.lam
    have hρ : ∀ x ∈ fv s, (FinPerm.swap a c * (FinPerm.swap (π a) c * π)) x = x := by
      intro x hx
      by_cases hxa : x = a
      · subst hxa
        simp only [FinPerm.mul_apply, FinPerm.swap_apply_left, FinPerm.swap_apply_right]
      · have hxfv : x ∈ fv (Raw.lam a s) := by simp [hxa, hx]
        have hpx : π x = x := h x hxfv
        have hxc : x ≠ c := fun he => hcs (he ▸ fv_subset_atoms s hx)
        have hxpa : x ≠ π a := fun he => hxa (π.val.injective (hpx.trans he))
        simp only [FinPerm.mul_apply, hpx,
          FinPerm.swap_apply_of_ne_of_ne hxpa hxc, FinPerm.swap_apply_of_ne_of_ne hxa hxc]
    have hfix := ih hρ
    have key := aeq_smul (FinPerm.swap a c) hfix
    rw [← mul_smul, ← mul_assoc, FinPerm.swap_swap, one_mul, mul_smul] at key
    exact key

/-- **`Tm` is a nominal set** over `Atom`/`FinPerm`, with support the free
variables. -/
noncomputable instance : NomSet Tm where
  supp := Tm.freeVars
  supp_supports := by
    refine Tm.ind fun t π h => ?_
    exact Tm.mk_eq (aeq_of_fixes_fv fun a ha => h a (by simpa using ha))
  supp_equivariant := by
    refine Tm.ind fun t π => ?_
    show Tm.freeVars (Tm.mk (π • t)) = (Tm.freeVars (Tm.mk t)).image (π ·)
    simp [fv_smul]

@[simp] theorem Tm.supp_mk (t : Raw) : NomSet.supp (Tm.mk t) = fv t := rfl

end CatCrypt.Nominal.Lambda
