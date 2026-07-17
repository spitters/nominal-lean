/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.NominalCoreBridge
import Nominal.Category.Nominal
import Nominal
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Equivalence

set_option autoImplicit false

/-!
# The Schanuel-topos identification, categorically: `Nom` vs finitely-supported `FinPerm`-sets

This file develops the category-level bridge on top of `NominalCoreBridge`, comparing the two
group actions that formalize nominal sets:

* `Nom` — the finite-support full subcategory of `Action Type PermAtom` (`PermAtom = Equiv.Perm ℕ`,
  the **full** permutation group), from `CatCrypt.Category.Nominal`;
* `NomFin` — the finite-support full subcategory of `Action Type FinPerm` (`FinPerm` = the
  **finitely-supported** permutations of the core atoms), the categorical form of "core nominal
  sets" defined here, exactly mirroring `Nom`.

## What is delivered

1. `GSetFin`, `SupportsFin`, `IsNominalFin`, `NomFin` — the `FinPerm`-side mirror of `Nom`.
2. `res : Nom ⥤ NomFin` — the restriction functor along `finPermToPerm : FinPerm →* PermAtom`
   (Mathlib's `Action.res`), lifted into the finite-support subcategory (support is preserved: the
   same support, transported along the atom equivalence, works).
3. `res` is **fully faithful** (`Nominal.instFaithfulRes`, `Nominal.instFullRes`). Faithfulness is
   inherited; **fullness is the substantive half of the Schanuel identification** — a
   `FinPerm`-equivariant map between two genuine `PermAtom`-actions with finite support is
   automatically `PermAtom`-equivariant, because every full permutation agrees, on the finite
   support of a point, with some finitely-supported one (`finPermToPerm_agree_on_finset`).
4. `extObj` — the object-level extension `ext`: a `FinPerm`-set carrying an *equivariant* support
   function extends to a genuine `PermAtom`-action (`Nom` object), generalizing
   `NominalCoreBridge.coreToGSet`. The round-trip `resExtIso : res.obj (extObj X …) ≅ X` proves
   **one of the two natural isos of the intended equivalence** (`res ∘ ext ≅ 𝟭`) for every such
   object.
5. On core objects: `coreObjFin α` presents a core `NomSet α` as an object of `NomFin`;
   `coreToNom_eq_extObj` shows the bridge `coreToNom` *is* `ext` applied to `coreObjFin α`
   (factoring it as `NomSet α ⟶ NomFin ⟶ Nom`); and
   `coreResExtIso : res.obj (coreToNom α) ≅ coreObjFin α` specializes the round-trip.

## Honest boundary — what is *not* assembled (a precise residual, not asserted anywhere)

The full equivalence `NomFin ≌ Nom` is **not** built here. Since `res` is fully faithful, the only
missing ingredient is **essential surjectivity**: extending an *arbitrary* finite-support
`FinPerm`-action to a `PermAtom`-action. For a general `NomFin` object this requires a *canonical
equivariant* support function (`supp (τ • x) = τ '' supp x`), equivalently the **least support** —
which exists only via the classical nominal lemma that finite supports are closed under
intersection (`Supports s x → Supports t x → Supports (s ∩ t) x`, a fresh-atom interpolation
argument). That lemma is **not** available in `CatCryptCore.Nominal`; it is exactly the residual
already flagged for the separated-product associator in `CatCrypt.Category.Nominal`. The extension
therefore succeeds precisely for objects that *carry* an equivariant support — the core-derived
objects above, whose extension is `coreToNom` — and the general functor `ext : NomFin ⥤ Nom` (hence
`res.asEquivalence`) is gated on that single missing lemma. No theorem below asserts the full
equivalence.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

namespace Nominal

open CatCrypt.Nominal

/-! ## Step 1 — the `FinPerm`-side mirror of `Nom` -/

/-- The ambient category of `G`-sets for `G = FinPerm`, the finitely-supported permutations of the
core atoms. This is the categorical home of "core nominal sets". -/
abbrev GSetFin : Type _ := Action (Type) CatCrypt.Nominal.FinPerm

namespace GSetFin

variable (X : GSetFin)

/-- Apply a `FinPerm`-set action to a point. As with `GSet.act`, the `End`-valued action
`X.ρ τ : End X.V` is a categorical endomorphism in Lean 4.30, so applying it to a point goes
through `ConcreteCategory.hom`. -/
abbrev act (τ : CatCrypt.Nominal.FinPerm) (x : X.V) : X.V := ConcreteCategory.hom (X.ρ τ) x

end GSetFin

/-- `s` **supports** `x` for the `FinPerm`-action: every finitely-supported permutation fixing `s`
pointwise fixes `x`. The `FinPerm`-side mirror of `Nominal.Supports`. -/
def SupportsFin (X : GSetFin) (s : Finset CatCrypt.Nominal.Atom) (x : X.V) : Prop :=
  ∀ τ : CatCrypt.Nominal.FinPerm, (∀ a ∈ s, τ a = a) → X.act τ x = x

/-- A `FinPerm`-set has finite support everywhere. The mirror of `IsNominal`. -/
def IsNominalFin (X : GSetFin) : Prop :=
  ∀ x : X.V, ∃ s : Finset CatCrypt.Nominal.Atom, SupportsFin X s x

/-- `NomFin`, the category of finitely-supported `FinPerm`-sets: the full subcategory cut out by
`IsNominalFin`. The categorical form of core nominal sets. -/
abbrev NomFin : Type _ := ObjectProperty.FullSubcategory IsNominalFin

/-- Package a `FinPerm`-set with a finite-support proof as an object of `NomFin`. -/
abbrev NomFin.of (X : GSetFin) (h : IsNominalFin X) : NomFin := ⟨X, h⟩

example : Category NomFin := inferInstance

/-! ## A support-agreement lemma on the full-permutation side

Two full permutations agreeing on a support of `x` act identically on `x`. This is the `GSet`
analogue of `NominalCoreBridge.nomSet_act_eq_of_agree`, and drives the fullness proof. -/

/-- If `s` supports `x` and `π₁`, `π₂` agree on `s`, then they act identically on `x`. -/
lemma act_eq_of_supports {X : GSet} {s : Finset Nominal.Atom} {x : X.V}
    (hs : Supports X s x) {π₁ π₂ : PermAtom} (h : ∀ a ∈ s, π₁ a = π₂ a) :
    X.act π₁ x = X.act π₂ x := by
  have hfix : ∀ a ∈ s, (π₁⁻¹ * π₂) a = a := by
    intro a ha
    simp [Equiv.Perm.mul_apply, ← h a ha]
  have key := hs (π₁⁻¹ * π₂) hfix
  calc X.act π₁ x
      = X.act π₁ (X.act (π₁⁻¹ * π₂) x) := by rw [key]
    _ = X.act (π₁ * (π₁⁻¹ * π₂)) x := (GSet.act_mul X _ _ x).symm
    _ = X.act π₂ x := by rw [← mul_assoc, mul_inv_cancel, one_mul]

/-! ## Step 2 — the restriction functor `res : Nom ⥤ NomFin`

Along `finPermToPerm : FinPerm →* PermAtom`, Mathlib's `Action.res` restricts a `PermAtom`-action
to a `FinPerm`-action, on the same carrier. We show it preserves finite support and lift it into
`NomFin`. -/

/-- The underlying restriction `GSet ⥤ GSetFin` along `finPermToPerm`. -/
noncomputable abbrev resGSet : GSet ⥤ GSetFin := Action.res _ finPermToPerm

/-- Restriction preserves finite support: a support finset for the full-`PermAtom` action, mapped
back through the atom equivalence, supports the restricted `FinPerm`-action. -/
lemma isNominalFin_resGSet {X : GSet} (hX : IsNominal X) :
    IsNominalFin (resGSet.obj X) := by
  intro x
  obtain ⟨s, hs⟩ := hX x
  refine ⟨s.image coreAtomEquiv.symm, ?_⟩
  intro τ hτ
  show X.act (finPermToPerm τ) x = x
  refine hs (finPermToPerm τ) ?_
  intro b hb
  have hmem : coreAtomEquiv.symm b ∈ s.image coreAtomEquiv.symm :=
    Finset.mem_image_of_mem _ hb
  have hfix := hτ (coreAtomEquiv.symm b) hmem
  simp only [CatCrypt.Nominal.FinPerm.apply_def] at hfix
  simp [finPermToPerm, Equiv.permCongr_apply, hfix]

/-- The restriction functor `Nom ⥤ NomFin`. -/
noncomputable def res : Nom ⥤ NomFin :=
  ObjectProperty.lift IsNominalFin (ObjectProperty.ι IsNominal ⋙ resGSet)
    (fun X => isNominalFin_resGSet X.property)

@[simp] lemma res_obj_obj (X : Nom) : (res.obj X).obj = resGSet.obj X.obj := rfl

/-! ## Step 3 (fullness) — the substantive half of Schanuel

`res` is fully faithful. Faithfulness is formal; fullness says a `FinPerm`-equivariant map between
finitely-supported `PermAtom`-actions is `PermAtom`-equivariant. -/

/-- Any full permutation agrees, on a given finite set of atoms, with some finitely-supported one
(read through the atom equivalence). The full-permutation transport of
`NominalCoreBridge.finPerm_agree_on_finset`. -/
theorem finPermToPerm_agree_on_finset (π : PermAtom) (s : Finset Nominal.Atom) :
    ∃ τ : CatCrypt.Nominal.FinPerm, ∀ b ∈ s, finPermToPerm τ b = π b := by
  obtain ⟨τ, hτ⟩ := finPerm_agree_on_finset (fromPermℕ π) (s.image coreAtomEquiv.symm)
  refine ⟨τ, fun b hb => ?_⟩
  have hmem : coreAtomEquiv.symm b ∈ s.image coreAtomEquiv.symm :=
    Finset.mem_image_of_mem _ hb
  have hτb := hτ (coreAtomEquiv.symm b) hmem
  simp only [CatCrypt.Nominal.FinPerm.apply_def] at hτb
  simp [finPermToPerm, fromPermℕ, Equiv.permCongr_apply, hτb]

/-- The `PermAtom`-equivariant preimage of a `FinPerm`-equivariant map between finitely-supported
`PermAtom`-actions: the same underlying function, now shown equivariant for the *full* group. -/
noncomputable def fullPreimage {X Y : Nom} (g : res.obj X ⟶ res.obj Y) :
    X ⟶ Y :=
  ObjectProperty.homMk
    { hom := g.hom.hom
      comm := by
        intro π
        apply ConcreteCategory.hom_ext; intro x
        show g.hom.hom (X.obj.act π x) = Y.obj.act π (g.hom.hom x)
        obtain ⟨sx, hsx⟩ := X.property x
        obtain ⟨sy, hsy⟩ := Y.property (g.hom.hom x)
        obtain ⟨τ, hτ⟩ := finPermToPerm_agree_on_finset π (sx ∪ sy)
        have hax : X.obj.act π x = X.obj.act (finPermToPerm τ) x :=
          act_eq_of_supports hsx (fun a ha => (hτ a (Finset.mem_union_left sy ha)).symm)
        have hay : Y.obj.act (finPermToPerm τ) (g.hom.hom x)
            = Y.obj.act π (g.hom.hom x) :=
          act_eq_of_supports hsy (fun a ha => hτ a (Finset.mem_union_right sx ha))
        have hcomm : g.hom.hom (X.obj.act (finPermToPerm τ) x)
            = Y.obj.act (finPermToPerm τ) (g.hom.hom x) := by
          simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (g.hom.comm τ) x
        rw [hax, hcomm, hay] }

instance instFaithfulRes : res.Faithful where
  map_injective {X Y} f₁ f₂ h := by
    apply InducedCategory.Hom.ext
    apply Action.Hom.ext
    exact congrArg (fun m => m.hom.hom) h

instance instFullRes : res.Full where
  map_surjective {X Y} g := ⟨fullPreimage g, by
    apply InducedCategory.Hom.ext
    apply Action.Hom.ext
    rfl⟩

/-! ## Step 3 (object-level extension) — `ext` for objects carrying an equivariant support

A `FinPerm`-set equipped with a *chosen equivariant* support function extends to a genuine
`PermAtom`-action (the Schanuel reconstruction), generalizing `NominalCoreBridge.coreToGSet` from
the `NomSet` data class to an arbitrary `GSetFin` object plus support data. The equivariance
hypothesis `hequiv` is exactly what a general `NomFin` object does not carry (see the module
residual); core objects supply it canonically via `NomSet.supp_equivariant`. -/

/-- Left-action law for a `FinPerm`-set: products act by composition. -/
lemma GSetFin.act_mul (X : GSetFin) (a b : CatCrypt.Nominal.FinPerm) (x : X.V) :
    X.act (a * b) x = X.act a (X.act b x) := by simp [GSetFin.act, map_mul]

/-- Two finitely-supported permutations agreeing on a support of `x` act identically on `x`
(`FinPerm`-side; the `GSetFin` analogue of `NominalCoreBridge.nomSet_act_eq_of_agree`). -/
lemma actFin_eq_of_agree {X : GSetFin} {τ₁ τ₂ : CatCrypt.Nominal.FinPerm}
    {s : Finset CatCrypt.Nominal.Atom} {x : X.V}
    (hsupp : SupportsFin X s x) (h : ∀ a ∈ s, τ₁ a = τ₂ a) :
    X.act τ₁ x = X.act τ₂ x := by
  have hfix : ∀ a ∈ s, (τ₁⁻¹ * τ₂) a = a := by
    intro a ha
    have e : (τ₁⁻¹ * τ₂) a = (τ₁⁻¹ * τ₁) a := by
      simp only [CatCrypt.Nominal.FinPerm.mul_apply]; rw [← h a ha]
    rw [e, inv_mul_cancel, CatCrypt.Nominal.FinPerm.one_apply]
  have key := hsupp (τ₁⁻¹ * τ₂) hfix
  symm
  calc X.act τ₂ x
      = X.act (τ₁ * (τ₁⁻¹ * τ₂)) x := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = X.act τ₁ (X.act (τ₁⁻¹ * τ₂) x) := GSetFin.act_mul X _ _ x
    _ = X.act τ₁ x := by rw [key]

/-- The reconstructed full-`PermAtom` action on a finitely-supported `FinPerm`-set with an
equivariant support function: act by any finitely-supported permutation agreeing with `π` on the
chosen support. -/
noncomputable def extGSet (X : GSetFin) (suppOf : X.V → Finset CatCrypt.Nominal.Atom)
    (hsupp : ∀ x, SupportsFin X (suppOf x) x)
    (hequiv : ∀ x (τ : CatCrypt.Nominal.FinPerm), suppOf (X.act τ x) = (suppOf x).image (τ ·)) :
    GSet where
  V := X.V
  ρ :=
    { toFun := fun π => TypeCat.ofHom (fun x => X.act (extendPerm (fromPermℕ π) (suppOf x)) x)
      map_one' := by
        apply ConcreteCategory.hom_ext; intro x
        show X.act (extendPerm (fromPermℕ 1) (suppOf x)) x = x
        rw [fromPermℕ_one]
        refine hsupp x _ ?_
        intro a ha
        rw [extendPerm_spec 1 _ a ha]; rfl
      map_mul' := fun π σ => by
        apply ConcreteCategory.hom_ext; intro x
        show X.act (extendPerm (fromPermℕ (π * σ)) (suppOf x)) x
            = X.act (extendPerm (fromPermℕ π)
                (suppOf (X.act (extendPerm (fromPermℕ σ) (suppOf x)) x)))
              (X.act (extendPerm (fromPermℕ σ) (suppOf x)) x)
        set σ' := extendPerm (fromPermℕ σ) (suppOf x) with hσ'
        rw [← GSetFin.act_mul]
        refine actFin_eq_of_agree (hsupp x) ?_
        intro a ha
        rw [extendPerm_spec (fromPermℕ (π * σ)) _ a ha, fromPermℕ_mul]
        have hσa : σ' a = fromPermℕ σ a := extendPerm_spec (fromPermℕ σ) _ a ha
        have hmem : fromPermℕ σ a ∈ suppOf (X.act σ' x) := by
          rw [hequiv x σ', ← hσa]
          exact Finset.mem_image_of_mem _ ha
        simp only [CatCrypt.Nominal.FinPerm.mul_apply]
        rw [hσa, extendPerm_spec (fromPermℕ π) _ (fromPermℕ σ a) hmem, Equiv.Perm.mul_apply] }

/-- The transported chosen support supports `x` for the reconstructed full-`PermAtom` action. -/
lemma extGSet_supports (X : GSetFin) (suppOf : X.V → Finset CatCrypt.Nominal.Atom)
    (hsupp : ∀ x, SupportsFin X (suppOf x) x)
    (hequiv : ∀ x (τ : CatCrypt.Nominal.FinPerm), suppOf (X.act τ x) = (suppOf x).image (τ ·))
    (x : X.V) :
    Supports (extGSet X suppOf hsupp hequiv) ((suppOf x).image coreAtomEquiv) x := by
  intro π hπ
  show X.act (extendPerm (fromPermℕ π) (suppOf x)) x = x
  refine hsupp x _ ?_
  intro a ha
  have hmem : coreAtomEquiv a ∈ (suppOf x).image coreAtomEquiv := Finset.mem_image_of_mem _ ha
  have hfix := hπ (coreAtomEquiv a) hmem
  rw [extendPerm_spec (fromPermℕ π) _ a ha]
  simp [fromPermℕ, Equiv.permCongr_apply, hfix]

/-- The reconstructed action is nominal (finitely supported). -/
lemma extGSet_isNominal (X : GSetFin) (suppOf : X.V → Finset CatCrypt.Nominal.Atom)
    (hsupp : ∀ x, SupportsFin X (suppOf x) x)
    (hequiv : ∀ x (τ : CatCrypt.Nominal.FinPerm), suppOf (X.act τ x) = (suppOf x).image (τ ·)) :
    IsNominal (extGSet X suppOf hsupp hequiv) :=
  fun x => ⟨_, extGSet_supports X suppOf hsupp hequiv x⟩

/-- The object-level extension `ext` into `Nom`, for a `FinPerm`-set with an equivariant support. -/
noncomputable def extObj (X : GSetFin) (suppOf : X.V → Finset CatCrypt.Nominal.Atom)
    (hsupp : ∀ x, SupportsFin X (suppOf x) x)
    (hequiv : ∀ x (τ : CatCrypt.Nominal.FinPerm), suppOf (X.act τ x) = (suppOf x).image (τ ·)) :
    Nom :=
  Nom.of (extGSet X suppOf hsupp hequiv) (extGSet_isNominal X suppOf hsupp hequiv)

/-! ## Step 4/5 — the extension on core objects, and the round-trip iso

For objects that carry an equivariant support — the core `NomSet α` objects — the extension is the
already-built `coreToNom`. We present the core object on the `NomFin` side (`coreObjFin`) and
exhibit the round-trip `res.obj (coreToNom α) ≅ coreObjFin α`. -/

/-- A core nominal set as a `FinPerm`-set (its native `MulAction`, as an `Action` object). -/
noncomputable def coreGSetFin (α : Type) [NomSet α] : GSetFin where
  V := α
  ρ :=
    { toFun := fun τ => TypeCat.ofHom (fun x => τ • x)
      map_one' := by apply ConcreteCategory.hom_ext; intro x; exact one_smul _ x
      map_mul' := fun a b => by apply ConcreteCategory.hom_ext; intro x; exact mul_smul a b x }

/-- A core nominal set is finitely supported for its `FinPerm`-action, via `NomSet.supp`. -/
lemma coreGSetFin_isNominalFin (α : Type) [NomSet α] : IsNominalFin (coreGSetFin α) :=
  fun x => ⟨@NomSet.supp α _ x, fun τ hτ => @NomSet.supp_supports α _ x τ hτ⟩

/-- A core nominal set as an object of `NomFin`. -/
noncomputable def coreObjFin (α : Type) [NomSet α] : NomFin :=
  NomFin.of (coreGSetFin α) (coreGSetFin_isNominalFin α)

/-- **Step 5 factorization.** The core→categorical bridge `coreToNom` is exactly the object-level
extension `extObj` applied to the core object `coreObjFin α` (with its canonical equivariant support
`NomSet.supp`). Thus `coreToNom` factors as `NomSet α ⟶ NomFin ⟶ Nom` through `ext`. -/
lemma coreToNom_eq_extObj (α : Type) [NomSet α] :
    coreToNom α = extObj (coreGSetFin α) (@NomSet.supp α _)
      (fun x => @NomSet.supp_supports α _ x)
      (fun x τ => @NomSet.supp_act_eq_image α _ x τ) := rfl

/-- The two conjugations cancel: transporting a `FinPerm` up to `PermAtom` and back is the identity
underlying permutation. -/
lemma fromPermℕ_finPermToPerm (τ : CatCrypt.Nominal.FinPerm) :
    fromPermℕ (finPermToPerm τ) = τ.val := by
  ext a
  simp [fromPermℕ, finPermToPerm, Equiv.permCongr_apply]

/-- The underlying `GSetFin` iso for the general round-trip: restricting the reconstructed
full-`PermAtom` action along `finPermToPerm` recovers the original `FinPerm`-action, on the same
carrier. -/
noncomputable def resExtGSetIso (X : GSetFin) (suppOf : X.V → Finset CatCrypt.Nominal.Atom)
    (hsupp : ∀ x, SupportsFin X (suppOf x) x)
    (hequiv : ∀ x (τ : CatCrypt.Nominal.FinPerm), suppOf (X.act τ x) = (suppOf x).image (τ ·)) :
    resGSet.obj (extGSet X suppOf hsupp hequiv) ≅ X :=
  Action.mkIso (Iso.refl _)
    (by
      intro τ
      apply ConcreteCategory.hom_ext; intro x
      simp only [Iso.refl_hom]
      show X.act (extendPerm (fromPermℕ (finPermToPerm τ)) (suppOf x)) x = X.act τ x
      rw [fromPermℕ_finPermToPerm]
      refine actFin_eq_of_agree (hsupp x) ?_
      intro a ha
      rw [extendPerm_spec τ.val _ a ha]
      rfl)

/-- **The round-trip `res ∘ ext ≅ 𝟭`** (object-level, for equivariant-support objects): restricting
the reconstructed full-`PermAtom` action of `extObj X …` recovers the original finitely-supported
`FinPerm`-set `X`. This is one of the two natural isomorphisms of the intended equivalence; it holds
for every object that carries an equivariant support (the other direction, and packaging as a
functor on all of `NomFin`, is the least-support residual documented in the module header). -/
noncomputable def resExtIso (X : GSetFin) (suppOf : X.V → Finset CatCrypt.Nominal.Atom)
    (hsupp : ∀ x, SupportsFin X (suppOf x) x)
    (hequiv : ∀ x (τ : CatCrypt.Nominal.FinPerm), suppOf (X.act τ x) = (suppOf x).image (τ ·)) :
    res.obj (extObj X suppOf hsupp hequiv) ≅ NomFin.of X (fun x => ⟨suppOf x, hsupp x⟩) :=
  ObjectProperty.isoMk _ (resExtGSetIso X suppOf hsupp hequiv)

/-- The round-trip specialized to core objects: `res.obj (coreToNom α) ≅ coreObjFin α`. Concretely
witnesses that the core→categorical bridge `coreToNom`, restricted back to `FinPerm`, is the
original core action. -/
noncomputable def coreResExtIso (α : Type) [NomSet α] :
    res.obj (coreToNom α) ≅ coreObjFin α :=
  resExtIso (coreGSetFin α) (@NomSet.supp α _)
    (fun x => @NomSet.supp_supports α _ x) (fun x τ => @NomSet.supp_act_eq_image α _ x τ)

end Nominal
