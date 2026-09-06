/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Nominal.Lambda

set_option autoImplicit false

/-!
# `Tm.lam` as name abstraction

The binder `Tm.lam a` factors through name abstraction: `Tm.lam a t = tmLam (abs a t)`.
The fv-based α-rename `Tm.lam_rename_fresh` and the some=any principle
`Tm.lam_some_any` follow from `abs_rename`.

## Main results

* `avoid` — an α-equivalent representative that avoids a chosen non-free atom.
* `Tm.lam_rename_fresh` — rename the bound name to any atom fresh for the term.
* `tmLam` and `Tm.lam_eq_tmLam` — the binder factors through `NameAbs Tm`.
* `Tm.lam_some_any` — the Gabbay–Pitts some=any principle for the binder.
-/

@[expose] public section

namespace CatCrypt.Nominal.Lambda

open CatCrypt.Nominal

/-- **Rename a bound name away.** If `c` is not free in `r`, some α-equivalent
`r'` avoids `c` entirely (as a bound name too). -/
theorem avoid (c : Atom) : ∀ r : Raw, c ∉ fv r → ∃ r', AEq r r' ∧ c ∉ atoms r'
  | .var a, h => ⟨.var a, .rfl _, by simpa using (by simpa using h : c ≠ a)⟩
  | .app s t, h => by
    obtain ⟨s', hs, hcs⟩ := avoid c s (fun hc => h (by simp [hc]))
    obtain ⟨t', ht, hct⟩ := avoid c t (fun hc => h (by simp [hc]))
    exact ⟨.app s' t', .app hs ht, by simp [hcs, hct]⟩
  | .lam a t, h => by
    by_cases hca : c = a
    · subst hca
      set d := Atom.fresh (insert c (atoms t)) with hd
      have hdmem := Atom.fresh_not_mem (insert c (atoms t))
      rw [← hd] at hdmem
      have hdc : d ≠ c := fun he => hdmem (by rw [he]; exact Finset.mem_insert_self _ _)
      have hdt : d ∉ atoms t := fun hc => hdmem (Finset.mem_insert_of_mem hc)
      refine ⟨.lam d (FinPerm.swap c d • t), AEq.rename c d t hdt, ?_⟩
      simp only [atoms_lam, atoms_smul, Finset.mem_insert, Finset.mem_image, not_or]
      refine ⟨fun he => hdc he.symm, ?_⟩
      rintro ⟨x, hx, hxe⟩
      by_cases hxd : x = d
      · exact hdt (hxd ▸ hx)
      · by_cases hxc : x = c
        · rw [hxc, FinPerm.swap_apply_left] at hxe; exact hdc hxe
        · rw [FinPerm.swap_apply_of_ne_of_ne hxc hxd] at hxe; exact hxc hxe
    · obtain ⟨t', ht, hct⟩ := avoid c t (fun hc => h (by simp [hca, hc]))
      exact ⟨.lam a t', AEq.lam ht, by simp [hca, hct]⟩

/-- **fv-based α-rename for `Tm.lam`.** Changing the bound name to any atom fresh
for the term (not only for a representative) gives an equal term. -/
theorem Tm.lam_rename_fresh (a c : Atom) (t : Tm) (hc : c ∉ Tm.freeVars t) (_hca : c ≠ a) :
    Tm.lam a t = Tm.lam c (FinPerm.swap a c • t) := by
  induction t using Tm.ind with
  | _ r =>
    obtain ⟨r', har, hcr'⟩ := avoid c r (by simpa using hc)
    have h1 : Tm.lam a (Tm.mk r) = Tm.mk (.lam a r') := by
      rw [Tm.mk_eq har]; rfl
    have h2 : Tm.lam c (FinPerm.swap a c • Tm.mk r) = Tm.mk (.lam c (FinPerm.swap a c • r')) := by
      rw [Tm.smul_mk, Tm.mk_eq (aeq_smul (FinPerm.swap a c) har)]; rfl
    rw [h1, h2]
    exact Tm.mk_eq (AEq.rename a c r' hcr')

/-- The compatibility of `Tm.lam` with α-equivalence of the abstraction. -/
theorem Tm.lam_absRel {a a' : Atom} {t t' : Tm} (h : AbsRel (a, t) (a', t')) :
    Tm.lam a t = Tm.lam a' t' := by
  refine NameAbs.absRel_respect_of_swap (fun a t => Tm.lam a t) ?_ a a' t t' h
  intro b c x hc hcb
  exact Tm.lam_rename_fresh b c x hc hcb

/-- **`Tm.lam` factors through name abstraction.** -/
noncomputable def tmLam : NameAbs Tm → Tm :=
  NameAbs.lift (fun a t => Tm.lam a t) (fun _ _ _ _ h => Tm.lam_absRel h)

@[simp] theorem tmLam_abs (a : Atom) (t : Tm) : tmLam (abs a t) = Tm.lam a t := rfl

/-- The syntactic binder **is** the nominal abstraction: `Tm.lam a t = tmLam (abs a t)`. -/
theorem Tm.lam_eq_tmLam (a : Atom) (t : Tm) : Tm.lam a t = tmLam (abs a t) := rfl

/-- **Some = any (freshness) for the binder.** Two atoms fresh for the term give
the same abstraction after the corresponding renaming — the Gabbay–Pitts
principle, inherited from `abs`. -/
theorem Tm.lam_some_any (a b c : Atom) (t : Tm)
    (hb : b ∉ Tm.freeVars t) (hc : c ∉ Tm.freeVars t) (hba : b ≠ a) (hca : c ≠ a) :
    Tm.lam b (FinPerm.swap a b • t) = Tm.lam c (FinPerm.swap a c • t) := by
  rw [← Tm.lam_rename_fresh a b t hb hba, ← Tm.lam_rename_fresh a c t hc hca]

end CatCrypt.Nominal.Lambda
