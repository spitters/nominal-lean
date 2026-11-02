/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import NominalIris.Camera
public import NominalIris.Separation
public import Nominal.FinPerm

/-!
# The denotation of the name camera in `NomProp`, and the permutation action on `NomProp`

The denotation `den` is a monoid morphism from the name camera (`NominalIris.Camera`) into
`NomProp` (`NominalIris.Separation`): `den_op`, `den_valid_iff`, and for two fragments
`den_freshRA_op` and `concrete_sep_iff_camera_valid`. So `freshName_sep_ne` follows from camera
validity (`freshName_sep_ne_via_camera`). `den` relates the camera to `NomProp`; no theorem
relates `NomProp` to the `iOwn` ownership `ownFresh` in `IProp`.

`FinPerm` acts on heap states by moving locations (`permState`) and on propositions by
precomposition (`permProp`). The action needs no finite support, so it is defined on all of
`NomProp`, which is not a nominal set. It preserves entailment, `∗`, `emp` and pure propositions
and sends `freshName a` to `freshName (π a)`; `freshName_sep_ne_perm` is `freshName_sep_ne`
carried along it.
-/

set_option autoImplicit false

@[expose] public section

namespace NominalIris

open Iris Iris.BI CMRA
open CatCrypt.Nominal (Atom FinPerm)
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
  change den (.valid ∅) = _
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
      · rw [ite_eq_left h, den_valid, NameSet.toFinset_union, den_valid, den_valid]
        exact (worldProp_sep ((NameSet.disjoint_iff a b).mp h)).symm
      · have hnd : ¬ Disjoint a.toFinset b.toFinset :=
          fun hd => h ((NameSet.disjoint_iff a b).mpr hd)
        rw [ite_eq_right h, den_error, den_valid, den_valid]
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

/-- `den` sends the camera product of two fragments to the separating conjunction of the two
fresh-name resources. -/
theorem den_freshRA_op (a b : Atom) :
    (den (freshRA a • freshRA b) : NomProp) ⊣⊢ iprop(freshName a ∗ freshName b) := by
  have h := den_op (freshRA a) (freshRA b)
  rwa [den_freshRA, den_freshRA] at h

/-! ## The permutation action on states and propositions -/

/-- `FinPerm` acts on heap states by moving locations: the value at location `(π a).val` is the
value of `σ` at `a.val`. -/
def permState (π : FinPerm) (σ : NomState) : NomState := fun i => σ (π⁻¹ ⟨i⟩).val

theorem permState_one (σ : NomState) : permState 1 σ = σ := by
  funext i; simp [permState]

theorem permState_mul (π₁ π₂ : FinPerm) (σ : NomState) :
    permState (π₁ * π₂) σ = permState π₁ (permState π₂ σ) := by
  funext i; simp [permState, mul_inv_rev]

theorem permState_inv_self (π : FinPerm) (σ : NomState) : permState π⁻¹ (permState π σ) = σ := by
  rw [← permState_mul, inv_mul_cancel, permState_one]

theorem permState_self_inv (π : FinPerm) (σ : NomState) : permState π (permState π⁻¹ σ) = σ := by
  rw [← permState_mul, mul_inv_cancel, permState_one]

/-- The state of a name-world moves with the image of the world. -/
theorem permState_toNS (π : FinPerm) (w : NameWorld) :
    permState π (toNS w) = toNS (w.image (π ·)) := by
  funext i
  have h : (⟨i⟩ : Atom) ∈ w.image (π ·) ↔ π⁻¹ ⟨i⟩ ∈ w := by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, hi⟩
      rw [← hi, ← FinPerm.mul_apply, inv_mul_cancel, FinPerm.one_apply]
      exact ha
    · intro h
      exact ⟨_, h, by rw [← FinPerm.mul_apply, mul_inv_cancel, FinPerm.one_apply]⟩
  simp only [permState, toNS_apply, h]

/-- The action commutes with the union of states. -/
theorem permState_union (π : FinPerm) (σ₁ σ₂ : NomState) :
    permState π (σ₁ ∪ σ₂) = permState π σ₁ ∪ permState π σ₂ := by
  funext i
  simp only [permState, nsUnion_apply]

/-- The action preserves disjointness of states. -/
theorem permState_disjoint {π : FinPerm} {σ₁ σ₂ : NomState} (h : σ₁ || σ₂) :
    permState π σ₁ || permState π σ₂ := fun i => h (π⁻¹ ⟨i⟩).val

/-- `FinPerm` acts on propositions by precomposition with the inverse action on states. This
action is defined on all of `NomProp`; it does not require finite support. -/
def permProp (π : FinPerm) (P : NomProp) : NomProp := fun σ => P (permState π⁻¹ σ)

theorem permProp_one (P : NomProp) : permProp 1 P = P := by
  funext σ; simp [permProp, permState_one]

theorem permProp_mul (π₁ π₂ : FinPerm) (P : NomProp) :
    permProp (π₁ * π₂) P = permProp π₁ (permProp π₂ P) := by
  funext σ; simp [permProp, mul_inv_rev, permState_mul]

/-- `permProp` is a group action of `FinPerm` on `NomProp`. -/
instance : MulAction FinPerm NomProp where
  smul := permProp
  one_smul := permProp_one
  mul_smul := permProp_mul

/-- The action preserves entailment. -/
theorem permProp_mono (π : FinPerm) {P Q : NomProp} (h : P ⊢ Q) :
    permProp π P ⊢ permProp π Q := fun _ hσ => h _ hσ

/-- Entailment holds of the images iff it holds of the originals. -/
theorem permProp_entails_iff (π : FinPerm) {P Q : NomProp} :
    (permProp π P ⊢ permProp π Q) ↔ (P ⊢ Q) := by
  refine ⟨fun h σ hσ => ?_, permProp_mono π⟩
  have := h (permState π σ) (by simpa [permProp, permState_inv_self] using hσ)
  simpa [permProp, permState_inv_self] using this

/-- The action commutes with the separating conjunction. -/
theorem permProp_sep (π : FinPerm) (P Q : NomProp) :
    permProp π iprop(P ∗ Q) = (iprop(permProp π P ∗ permProp π Q) : NomProp) := by
  funext σ
  apply propext
  constructor
  · rintro ⟨σ₁, σ₂, hu, hd, h₁, h₂⟩
    refine ⟨permState π σ₁, permState π σ₂, ?_, permState_disjoint hd, ?_, ?_⟩
    · rw [← permState_union, ← hu, permState_self_inv]
    · simpa [permProp, permState_inv_self] using h₁
    · simpa [permProp, permState_inv_self] using h₂
  · rintro ⟨σ₁, σ₂, hu, hd, h₁, h₂⟩
    exact ⟨permState π⁻¹ σ₁, permState π⁻¹ σ₂, by rw [hu, permState_union],
      permState_disjoint hd, h₁, h₂⟩

/-- The action fixes `emp`. -/
theorem permProp_emp (π : FinPerm) : permProp π (emp : NomProp) = emp := by
  funext σ
  apply propext
  constructor
  · intro h
    have h' : permState π⁻¹ σ = ∅ := h
    change σ = ∅
    rw [← permState_self_inv π σ, h']
    rfl
  · intro h
    have h' : σ = ∅ := h
    subst h'
    rfl

/-- The action fixes pure propositions, which do not read the state: an unfolding of
`permProp`. -/
theorem permProp_pure (π : FinPerm) (φ : Prop) :
    permProp π (iprop(⌜φ⌝) : NomProp) = iprop(⌜φ⌝) := rfl

/-- The action on the world proposition is the image of the world. -/
theorem permProp_worldProp (π : FinPerm) (w : NameWorld) :
    permProp π (worldProp w) = worldProp (w.image (π ·)) := by
  funext σ
  apply propext
  simp only [permProp, worldProp]
  constructor
  · intro h; rw [← permState_self_inv π σ, h, permState_toNS]
  · intro h; rw [h, permState_toNS, ← Finset.image_comp]
    simp [Function.comp_def]

/-- **`freshName` is equivariant.** The image of `freshName a` is `freshName (π a)`. -/
theorem permProp_freshName (π : FinPerm) (a : Atom) :
    permProp π (freshName a) = freshName (π a) := by
  rw [freshName_eq_worldProp, permProp_worldProp, Finset.image_singleton, freshName_eq_worldProp]

/-- The image of the premise of `freshName_sep_ne` at `a, b` is its premise at `π a, π b`. -/
theorem permProp_freshName_sep (π : FinPerm) (a b : Atom) :
    permProp π iprop(freshName a ∗ freshName b) =
      (iprop(freshName (π a) ∗ freshName (π b)) : NomProp) := by
  rw [permProp_sep, permProp_freshName, permProp_freshName]

/-- `freshName_sep_ne` commutes with the action: applying `permProp π` to the law at `a, b` and
rewriting by `permProp_freshName_sep` gives the law at `π a, π b`, and the conclusions `a ≠ b` and
`π a ≠ π b` are equivalent. -/
theorem freshName_sep_ne_perm (π : FinPerm) (a b : Atom) :
    (iprop(freshName (π a) ∗ freshName (π b)) : NomProp) ⊢ iprop(⌜π a ≠ π b⌝) := by
  have h := permProp_mono π (freshName_sep_ne a b)
  rw [permProp_freshName_sep, permProp_pure] at h
  exact h.trans (pure_mono fun hab he => hab (π.val.injective he))

/-- `den` intertwines the action on fragments and on propositions. -/
theorem permProp_den_freshRA (π : FinPerm) (a : Atom) :
    permProp π (den (freshRA a)) = den (freshRA (π a)) := by
  rw [den_freshRA, den_freshRA, permProp_freshName]

end NominalIris
