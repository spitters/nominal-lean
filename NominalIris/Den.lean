/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import NominalIris.Camera
public import NominalIris.Separation

set_option autoImplicit false

/-!
# The camera ↔ concrete-BI equivalence, over nominal `Atom`

Bridges the `Atom` name camera (`NominalGhostAtom`) to the `Atom` nominal-
separation BI (`NominalBIAtom`): the denotation `den` is a monoid morphism from
the camera into the concrete BI, so the concrete headline `freshName_sep_ne` is
the image of camera validity. This is the `ℕ`-version equivalence, rebased onto
`Atom` so the whole stack shares one framework.
-/

@[expose] public section

namespace NominalIris

open Iris Iris.BI CMRA
open CatCrypt.Nominal (Atom)
open DisjointLeibnizSet

/-- The `False` proposition, the denotation of the invalid element. -/
def nomFalse : NomProp := fun _ => False

/-- The **denotation** of a name-camera element as a concrete nominal
proposition. -/
def den : NameRA → NomProp
  | .valid w => worldProp w.toFinset
  | .error   => nomFalse

@[simp] theorem den_valid (w : NameSet) : den (.valid w) = worldProp w.toFinset := rfl
@[simp] theorem den_error : den .error = nomFalse := rfl

theorem den_freshRA (a : Atom) : den (freshRA a) = freshName a := by
  rw [freshRA, den_valid, NameSet.toFinset_singleton, freshName_eq_worldProp]

theorem den_unit : den (UCMRA.unit : NameRA) = (emp : NomProp) := by
  show den (.valid ∅) = _
  rw [den_valid, NameSet.toFinset_empty, worldProp_empty]

theorem nomFalse_sep (Q : NomProp) : (iprop(nomFalse ∗ Q) : NomProp) = nomFalse := by
  funext σ; apply propext
  exact ⟨fun ⟨_, _, _, _, h, _⟩ => h.elim, fun h => h.elim⟩

theorem sep_nomFalse (P : NomProp) : (iprop(P ∗ nomFalse) : NomProp) = nomFalse := by
  funext σ; apply propext
  exact ⟨fun ⟨_, _, _, _, _, h⟩ => h.elim, fun h => h.elim⟩

/-- **Camera `•` ↦ separating `∗`, unconditionally.** -/
theorem den_op (x y : NameRA) : (den (x • y) : NomProp) ⊣⊢ iprop(den x ∗ den y) := by
  cases x with
  | error => rw [op_error_left, den_error, nomFalse_sep]; exact .rfl
  | valid a =>
    cases y with
    | error => rw [op_valid_error, den_error, sep_nomFalse]; exact .rfl
    | valid b =>
      rw [op_valid_valid]
      by_cases h : a ## b
      · rw [if_pos h, den_valid, NameSet.toFinset_union, den_valid, den_valid]
        exact (worldProp_sep ((NameSet.disjoint_iff a b).mp h)).symm
      · have hnd : ¬ Disjoint a.toFinset b.toFinset :=
          fun hd => h ((NameSet.disjoint_iff a b).mpr hd)
        rw [if_neg h, den_error, den_valid, den_valid]
        constructor
        · intro σ hσ; exact hσ.elim
        · intro σ hσ; exact (hnd (worldProp_sep_disjoint a.toFinset b.toFinset σ hσ)).elim

/-- **Camera validity ↦ satisfiability.** -/
theorem den_valid_iff (x : NameRA) : (∃ σ, den x σ) ↔ ✓ x := by
  cases x with
  | error => exact ⟨fun ⟨_, hσ⟩ => hσ.elim, fun hv => hv.elim⟩
  | valid w => exact ⟨fun _ => True.intro, fun _ => ⟨toNS w.toFinset, rfl⟩⟩

/-- **The equivalence.** Separability of the two concrete fresh-name resources is
camera validity of the combined fragments. -/
theorem concrete_sep_iff_camera_valid (a b : Atom) :
    (∃ σ, (iprop(freshName a ∗ freshName b) : NomProp) σ) ↔ ✓ (freshRA a • freshRA b) := by
  rw [← den_valid_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    have hσ' : (iprop(den (freshRA a) ∗ den (freshRA b)) : NomProp) σ := by
      rw [den_freshRA, den_freshRA]; exact hσ
    exact (den_op (freshRA a) (freshRA b)).mpr σ hσ'
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    have hσ' := (den_op (freshRA a) (freshRA b)).mp σ hσ
    rw [den_freshRA, den_freshRA] at hσ'
    exact hσ'

/-- **The concrete headline law, recovered from the camera.** -/
theorem freshName_sep_ne_via_camera (a b : Atom) :
    (iprop(freshName a ∗ freshName b) : NomProp) ⊢ iprop(⌜a ≠ b⌝) := by
  intro σ hσ
  exact (freshRA_valid_op_iff a b).mp ((concrete_sep_iff_camera_valid a b).mp ⟨σ, hσ⟩)

end NominalIris
