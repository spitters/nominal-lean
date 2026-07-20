/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/
import Iris.ProofMode
import Iris.Instances.Classical.Instance
import Nominal.Atom

set_option autoImplicit false

/-!
# Nominal separation as a BI, over nominal `Atom`

The nominal-separation BI (`freshName a ∗ freshName b ⊢ ⌜a ≠ b⌝`) over
nominal-lean's `Atom`, so it shares the framework with the nominal λ-terms and
the name camera. The iris-lean classical heap state is `ℕ`-indexed; an atom `a`
occupies location `a.val` (`Atom ≅ ℕ`), so name-worlds embed faithfully.

Permutation and equivariance for the nominal objects — name-worlds
(`Finset Atom`) and terms — use nominal-lean's `NomSet` / `FinPerm` action.
`NomProp` is not itself a nominal set: not every proposition has finite support.
-/

namespace NominalIris

open Iris.BI
open Iris.Instances.Data
open CatCrypt.Nominal (Atom)

/-- A **name-world**: a finite set of atoms. -/
abbrev NameWorld : Type := Finset Atom

/-- The nominal state model: allocated-or-not per `ℕ` location (trivial payload). -/
abbrev NomState : Type := State Unit

/-- Nominal propositions: iris-lean's classical heap BI over `NomState`. -/
abbrev NomProp : Type := Iris.Instances.Classical.HeapProp Unit

/-- Realise a name-world as a nominal state: `result ()` at location `a.val` for
each `a` in the world, `unknown` elsewhere. -/
def toNS (w : NameWorld) : NomState :=
  fun i => if (⟨i⟩ : Atom) ∈ w then .result () else .unknown

theorem nsUnion_apply (σ₁ σ₂ : NomState) (i : Nat) :
    (σ₁ ∪ σ₂) i = (match σ₁ i, σ₂ i with
      | .unknown , .unknown  => .unknown
      | .result x, .unknown  => .result x
      | .unknown , .result y => .result y
      | _        , _         => .conflict) := by
  show Union.union σ₁ σ₂ i = _
  simp only [Union.union]
  cases σ₁ i <;> cases σ₂ i <;> rfl

theorem toNS_apply (w : NameWorld) (i : Nat) :
    toNS w i = if (⟨i⟩ : Atom) ∈ w then .result () else .unknown := rfl

theorem mem_iff_val (a : Atom) (w : NameWorld) : (⟨a.val⟩ : Atom) ∈ w ↔ a ∈ w := by
  rw [show (⟨a.val⟩ : Atom) = a from rfl]

theorem toNS_empty : toNS ∅ = (∅ : NomState) := by
  funext i; rw [toNS_apply, if_neg (Finset.notMem_empty _)]; rfl

theorem toNS_injective : Function.Injective toNS := by
  intro w₁ w₂ h
  ext a
  have ha := congrFun h a.val
  simp only [toNS_apply, show (⟨a.val⟩ : Atom) = a from rfl] at ha
  by_cases h1 : a ∈ w₁ <;> by_cases h2 : a ∈ w₂ <;> simp_all

theorem toNS_disjoint_iff (w₁ w₂ : NameWorld) :
    (toNS w₁ || toNS w₂) ↔ Disjoint w₁ w₂ := by
  rw [Finset.disjoint_left]
  constructor
  · intro h a ha1 ha2
    rcases h a.val with h1 | h1
    · rw [toNS_apply, if_pos (by simpa using ha1)] at h1; exact absurd h1 (by simp)
    · rw [toNS_apply, if_pos (by simpa using ha2)] at h1; exact absurd h1 (by simp)
  · intro h i
    by_cases hi1 : (⟨i⟩ : Atom) ∈ w₁
    · exact Or.inr (by rw [toNS_apply, if_neg (h hi1)])
    · exact Or.inl (by rw [toNS_apply, if_neg hi1])

theorem toNS_union {w₁ w₂ : NameWorld} (h : Disjoint w₁ w₂) :
    toNS (w₁ ∪ w₂) = toNS w₁ ∪ toNS w₂ := by
  funext i
  rw [nsUnion_apply]
  simp only [toNS_apply, Finset.mem_union]
  rw [Finset.disjoint_left] at h
  by_cases h1 : (⟨i⟩ : Atom) ∈ w₁ <;> by_cases h2 : (⟨i⟩ : Atom) ∈ w₂ <;> simp_all

/-- The proposition "the world is exactly `w`". -/
def worldProp (w : NameWorld) : NomProp := fun σ => σ = toNS w

/-- The singleton state for atom `a`. -/
def singletonState (a : Atom) : NomState :=
  fun i => if i = a.val then .result () else .unknown

theorem singletonState_eq (a : Atom) : singletonState a = toNS {a} := by
  funext i
  simp only [singletonState, toNS_apply, Finset.mem_singleton, Atom.ext_iff]

/-- The **fresh-name resource**: the world holding exactly the name `a`. -/
def freshName (a : Atom) : NomProp := fun σ => σ = singletonState a

theorem freshName_eq_worldProp (a : Atom) : freshName a = worldProp {a} := by
  unfold freshName worldProp; rw [singletonState_eq]

theorem worldProp_empty : worldProp (∅ : NameWorld) = (emp : NomProp) := by
  unfold worldProp; rw [toNS_empty]; rfl

/-- **Distinct-support law.** `worldProp w₁ ∗ worldProp w₂` forces the supports
disjoint. -/
theorem worldProp_sep_disjoint (w₁ w₂ : NameWorld) :
    (worldProp w₁ ∗ worldProp w₂ : NomProp) ⊢ iprop(⌜Disjoint w₁ w₂⌝) := by
  rintro σ ⟨σ₁, σ₂, _, hd, h1, h2⟩
  subst h1; subst h2
  exact (toNS_disjoint_iff w₁ w₂).mp hd

/-- On disjoint supports, `∗` of two worlds is the union world. -/
theorem worldProp_sep {w₁ w₂ : NameWorld} (h : Disjoint w₁ w₂) :
    (worldProp w₁ ∗ worldProp w₂ : NomProp) ⊣⊢ worldProp (w₁ ∪ w₂) := by
  constructor
  · rintro σ ⟨σ₁, σ₂, hu, _, h1, h2⟩
    subst h1; subst h2
    show σ = toNS (w₁ ∪ w₂); rw [hu, toNS_union h]
  · rintro σ hσ
    refine ⟨toNS w₁, toNS w₂, ?_, (toNS_disjoint_iff w₁ w₂).mpr h, rfl, rfl⟩
    show σ = toNS w₁ ∪ toNS w₂; rw [hσ, toNS_union h]

/-- **Headline nominal law.** Two distinct fresh names are separated. -/
theorem freshName_sep_ne (a b : Atom) :
    (freshName a ∗ freshName b : NomProp) ⊢ iprop(⌜a ≠ b⌝) := by
  rintro σ ⟨σ₁, σ₂, _, hd, h1, h2⟩
  subst h1; subst h2
  intro hab; subst hab
  rcases hd a.val with h | h <;> simp [singletonState] at h

end NominalIris
