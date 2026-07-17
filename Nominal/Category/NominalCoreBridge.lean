/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal
import Nominal.Category.Nominal

set_option autoImplicit false

/-!
# Bridge between the two formalizations of nominal sets

Nominal sets are formalized twice in this development, with **different permutation groups** and
**different atom types**:

* **Core** (`CatCryptCore.Nominal`): `NomSet α extends MulAction FinPerm α` with a chosen
  finite `supp`. The acting group is `FinPerm`, the *finitely-supported* permutations
  (`{π : Equiv.Perm Atom // IsFinitelySupported π}`), a **subgroup** of the full permutation
  group. Its atom type is `structure Atom where val : ℕ`.
* **Categorical** (`CatCrypt.Category.Nominal`): `GSet := Action Type PermAtom` with
  `PermAtom := Equiv.Perm Atom` the **full** permutation group and `Atom := ℕ`; `IsNominal`/`Nom`
  cut out the finite-support full subcategory.

This file builds the group-level and object-level bridge between the two.

## What is delivered

1. **Atom bridge** — `coreAtomEquiv : CatCrypt.Nominal.Atom ≃ ℕ`, the (trivial) unwrapping of the
   one-field structure.
2. **Group bridge** — `finPermToPerm : FinPerm →* PermAtom`, a genuine monoid/group hom: the
   subtype coercion `FinPerm → Equiv.Perm (core Atom)` conjugated by `coreAtomEquiv` into
   `Equiv.Perm ℕ`.
3. **Object bridge** — `coreToGSet α`/`coreToNom α`: every core `NomSet α` is presented as a
   categorical object of the finite-support subcategory `Nom`, on the **same carrier** `α`.

## The step-3 direction, and why it is not obstructed

The naive reading of step 3 — "restrict the full-`PermAtom` action to `FinPerm`" — is backwards.
The core records only the action of the **smaller** group `FinPerm`; the categorical `GSet`
requires an action of the **larger** full group `Equiv.Perm ℕ`. Restriction goes the wrong way;
one must *extend* the `FinPerm`-action to the full group, and extending a homomorphism from a
subgroup to the whole group is not possible in general.

Here it **is** possible, and canonically so, precisely because of the finite-support data — this
is the classical **Schanuel-topos** identification: nominal sets over `FinPerm` are the same as
the finitely-supported (continuous) sets for the full permutation group. The reconstruction
(`fullSmul`): to act by an arbitrary `π : Equiv.Perm Atom` on `x`, choose any finitely-supported
`τ` agreeing with `π` on the finite support `supp x`, and set `π • x := τ • x`.

* **Existence** of such a `τ` is `finPerm_agree_on_finset` (an induction on the finite set: the
  transposition fix-up is well defined because `τ'` is already injective, so `τ' a` cannot collide
  with the images of the previously-handled atoms).
* **Well-definedness** (`nomSet_act_eq_of_agree`) is the defining property of support: two
  finitely-supported permutations agreeing on a support of `x` act identically on `x`.
* The two **action laws** `fullSmul_one` and `fullSmul_mul` then hold; `fullSmul_mul` is the
  substantive one and uses the core `supp`-equivariance to relocate the middle support.

So step 3 succeeds in full: `coreToGSet α` is a bona fide `GSet` and `coreToGSet_isNominal` places
it in `Nom`.

## Honest boundary (what is *not* built here)

This is the **object/group** level of the bridge, not a full categorical equivalence. Not
provided:

* functoriality — a functor `(core nominal category) ⥤ Nom` acting on equivariant maps, and the
  reverse functor `Nom ⥤ (core)` restricting a full-`Perm ℕ` action to `FinPerm`;
* the proof that these two functors form an **equivalence of categories** (the Schanuel-topos
  statement at full strength), i.e. that `coreToGSet` is essentially surjective and fully
  faithful. The reverse object map (categorical finite-support `GSet` ⟶ core `NomSet`, restricting
  along `finPermToPerm` and reading off a `supp`) is routine but not carried out.

These are stated as a precise residual rather than asserted; no theorem below claims them.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

namespace Nominal

/-- The atom bridge: the core atom structure `{val : ℕ}` is equivalent to the categorical
atom type `ℕ`. -/
def coreAtomEquiv : CatCrypt.Nominal.Atom ≃ Nominal.Atom where
  toFun a := a.val
  invFun n := ⟨n⟩
  left_inv a := by cases a; rfl
  right_inv n := rfl

/-- The group bridge: the finitely-supported permutations embed into the full permutation group
of `ℕ` as a group hom, by conjugating the subtype coercion with `coreAtomEquiv`. -/
noncomputable def finPermToPerm : CatCrypt.Nominal.FinPerm →* Nominal.PermAtom where
  toFun π := coreAtomEquiv.permCongr π.val
  map_one' := by
    simp only [CatCrypt.Nominal.FinPerm.one_val]; rfl
  map_mul' π₁ π₂ := by
    simp only [CatCrypt.Nominal.FinPerm.mul_val]
    ext a : 1
    simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

/-! ## Step 3 scaffolding: extending a full permutation on a finite set -/

open CatCrypt.Nominal in
/-- Any permutation of atoms agrees, on a given finite set, with some finitely-supported
permutation. This is the key extension lemma making the full-`Perm` action reconstructible
from the `FinPerm` action together with finite support. -/
theorem finPerm_agree_on_finset (π : Equiv.Perm CatCrypt.Nominal.Atom)
    (s : Finset CatCrypt.Nominal.Atom) :
    ∃ τ : CatCrypt.Nominal.FinPerm, ∀ a ∈ s, τ a = π a := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, by simp⟩
  | insert a s' ha ih =>
    obtain ⟨τ', hτ'⟩ := ih
    by_cases hval : τ' a = π a
    · refine ⟨τ', ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hval
      · exact hτ' x hx'
    · refine ⟨CatCrypt.Nominal.FinPerm.swap (τ' a) (π a) * τ', ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · simp
      · have hx_ne_a : x ≠ a := fun h => ha (h ▸ hx')
        have h1 : τ' x = π x := hτ' x hx'
        have hne1 : τ' x ≠ τ' a := by
          intro h
          exact hx_ne_a (τ'.val.injective (by simpa using h))
        have hne2 : τ' x ≠ π a := by
          rw [h1]; exact fun h => hx_ne_a (π.injective h)
        simp only [CatCrypt.Nominal.FinPerm.mul_apply]
        rw [CatCrypt.Nominal.FinPerm.swap_apply_of_ne_of_ne hne1 hne2, h1]

/-- A choice of finitely-supported permutation agreeing with `π` on `s`. -/
noncomputable def extendPerm (π : Equiv.Perm CatCrypt.Nominal.Atom)
    (s : Finset CatCrypt.Nominal.Atom) : CatCrypt.Nominal.FinPerm :=
  (finPerm_agree_on_finset π s).choose

theorem extendPerm_spec (π : Equiv.Perm CatCrypt.Nominal.Atom)
    (s : Finset CatCrypt.Nominal.Atom) (a : CatCrypt.Nominal.Atom) (ha : a ∈ s) :
    extendPerm π s a = π a :=
  (finPerm_agree_on_finset π s).choose_spec a ha

open CatCrypt.Nominal in
/-- Two finitely-supported permutations that agree on a support of `x` act identically on `x`. -/
theorem nomSet_act_eq_of_agree {α : Type*} [NomSet α]
    {τ₁ τ₂ : FinPerm} {s : Finset CatCrypt.Nominal.Atom} {x : α}
    (hsupp : CatCrypt.Nominal.Supports s x) (h : ∀ a ∈ s, τ₁ a = τ₂ a) :
    τ₁ • x = τ₂ • x := by
  have hfix : ∀ a ∈ s, (τ₁⁻¹ * τ₂) a = a := by
    intro a ha
    have e : (τ₁⁻¹ * τ₂) a = (τ₁⁻¹ * τ₁) a := by
      simp only [FinPerm.mul_apply]; rw [← h a ha]
    rw [e, inv_mul_cancel, FinPerm.one_apply]
  have hact := hsupp (τ₁⁻¹ * τ₂) hfix
  have key : τ₂ • x = τ₁ • x := by
    calc τ₂ • x = (τ₁ * (τ₁⁻¹ * τ₂)) • x := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      _ = τ₁ • ((τ₁⁻¹ * τ₂) • x) := mul_smul _ _ _
      _ = τ₁ • x := by rw [hact]
  exact key.symm

open CatCrypt.Nominal in
/-- The reconstructed full-`Perm` action on a core nominal set: act by any finitely-supported
permutation agreeing with `π` on the (finite) support of `x`. -/
noncomputable def fullSmul {α : Type*} [NomSet α]
    (π : Equiv.Perm CatCrypt.Nominal.Atom) (x : α) : α :=
  extendPerm π (NomSet.supp x) • x

open CatCrypt.Nominal in
theorem fullSmul_eq_self_of_fixes {α : Type*} [NomSet α]
    {π : Equiv.Perm CatCrypt.Nominal.Atom} {x : α}
    (h : ∀ a ∈ NomSet.supp x, π a = a) : fullSmul π x = x :=
  NomSet.supp_supports x _ (fun a ha => by rw [extendPerm_spec π _ a ha]; exact h a ha)

open CatCrypt.Nominal in
theorem fullSmul_one {α : Type*} [NomSet α] (x : α) : fullSmul 1 x = x :=
  fullSmul_eq_self_of_fixes (fun _ _ => rfl)

open CatCrypt.Nominal in
theorem fullSmul_mul {α : Type*} [NomSet α]
    (π σ : Equiv.Perm CatCrypt.Nominal.Atom) (x : α) :
    fullSmul (π * σ) x = fullSmul π (fullSmul σ x) := by
  set σ' := extendPerm σ (NomSet.supp x) with hσ'
  show extendPerm (π * σ) (NomSet.supp x) • x
      = extendPerm π (NomSet.supp (σ' • x)) • (σ' • x)
  rw [← mul_smul]
  refine nomSet_act_eq_of_agree (NomSet.supp_supports x) ?_
  intro a ha
  rw [extendPerm_spec (π * σ) _ a ha]
  have hσa : σ' a = σ a := extendPerm_spec σ _ a ha
  have hmem : σ a ∈ NomSet.supp (σ' • x) := by
    rw [NomSet.supp_act_eq_image, ← hσa]
    exact Finset.mem_image_of_mem _ ha
  simp only [FinPerm.mul_apply]
  rw [hσa, extendPerm_spec π _ (σ a) hmem, Equiv.Perm.mul_apply]

/-- Transport a full permutation of `ℕ` to a full permutation of the core `Atom` structure. -/
noncomputable def fromPermℕ (π : Nominal.PermAtom) : Equiv.Perm CatCrypt.Nominal.Atom :=
  coreAtomEquiv.symm.permCongr π

theorem fromPermℕ_one : fromPermℕ 1 = 1 := rfl

theorem fromPermℕ_mul (a b : Nominal.PermAtom) :
    fromPermℕ (a * b) = fromPermℕ a * fromPermℕ b := by
  ext x : 1
  simp [fromPermℕ, Equiv.permCongr_apply, Equiv.Perm.mul_apply]

open CatCrypt.Nominal in
/-- A core nominal set presented as a categorical `G`-set: the reconstructed full-`Perm ℕ`
action, transported from the `FinPerm` action via finite support. -/
noncomputable def coreToGSet (α : Type) [NomSet α] : GSet where
  V := α
  ρ :=
    { toFun := fun π => TypeCat.ofHom (fun x => fullSmul (fromPermℕ π) x)
      map_one' := by
        apply ConcreteCategory.hom_ext; intro x
        show fullSmul (fromPermℕ 1) x = x
        rw [fromPermℕ_one, fullSmul_one]
      map_mul' := fun a b => by
        apply ConcreteCategory.hom_ext; intro x
        show fullSmul (fromPermℕ (a * b)) x = fullSmul (fromPermℕ a) (fullSmul (fromPermℕ b) x)
        rw [fromPermℕ_mul, fullSmul_mul] }

open CatCrypt.Nominal in
/-- The core support of `x`, transported along `coreAtomEquiv`, supports `x` for the
full-`Perm ℕ` categorical action. -/
theorem coreToGSet_supports (α : Type) [NomSet α] (x : α) :
    Supports (coreToGSet α) ((NomSet.supp x).image coreAtomEquiv) x := by
  intro π hπ
  show fullSmul (fromPermℕ π) x = x
  refine fullSmul_eq_self_of_fixes (fun b hb => ?_)
  have hmem : coreAtomEquiv b ∈ (NomSet.supp x).image coreAtomEquiv :=
    Finset.mem_image_of_mem _ hb
  have hfix := hπ (coreAtomEquiv b) hmem
  simp [fromPermℕ, Equiv.permCongr_apply, hfix]

open CatCrypt.Nominal in
/-- The presented `G`-set is finitely supported (nominal): every element is supported by the
transported core support. -/
theorem coreToGSet_isNominal (α : Type) [NomSet α] : IsNominal (coreToGSet α) :=
  fun x => ⟨_, coreToGSet_supports α x⟩

/-- A core nominal set as an object of the categorical `Nom` (finite-support subcategory). -/
noncomputable def coreToNom (α : Type) [CatCrypt.Nominal.NomSet α] : Nom :=
  Nom.of (coreToGSet α) (coreToGSet_isNominal α)

end Nominal
