/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.NominalCoreEquivalence
import Nominal.Category.NominalMonoidal

set_option autoImplicit false

/-!
# Completing the Schanuel identification: `NomFin ≌ Nom`

`CatCrypt.Category.NominalCoreEquivalence` proves the restriction functor `res : Nom ⥤ NomFin`
fully faithful and builds the extension of any `FinPerm`-set *that carries an equivariant support*.
Its single residual is **essential surjectivity**: extending an *arbitrary* finite-support
`FinPerm`-object needs a canonical equivariant support, i.e. the **least support**, which exists
only once finite supports are closed under intersection.

This file supplies exactly that lemma over `FinPerm` (`supportsFin_inter`, the fresh-atom
interpolation argument, mirroring `Nominal.supports_inter` over the full `PermAtom`), builds the
canonical least support `suppFin` with its equivariance, packages the extension functor
`extFunctor : NomFin ⥤ Nom`, and assembles the equivalence.

## What is delivered

1. `supportsFin_inter` — finite `SupportsFin`-supports are closed under intersection.
2. `suppFin` — the canonical least support of a `NomFin` element, with `suppFin_supports`,
   `suppFin_le` and `suppFin_equivariant` (least supports are equivariant).
3. `extFunctor : NomFin ⥤ Nom` — the extension functor (essential-surjectivity witness).
4. `extResIso` — the round-trip `ext ∘ res ≅ 𝟭` on `Nom`.
5. `instEssSurjRes`, `nomFinEquivNom : NomFin ≌ Nom` — the full equivalence of categories.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

open scoped Classical

namespace Nominal

open CatCrypt.Nominal

/-! ## Step 0 — small `GSetFin`/`FinPerm` support helpers -/

/-- The `FinPerm`-action sends the identity to the identity. -/
lemma GSetFin.act_one (X : GSetFin) (x : X.V) : X.ρ 1 x = x := by
  rw [Action.ρ_one]; rfl

/-- A `FinPerm.swap` of two atoms both outside a `SupportsFin`-support fixes the element. -/
lemma swapFin_apply_eq_self {X : GSetFin} {s : Finset CatCrypt.Nominal.Atom} {x : X.V}
    (hs : SupportsFin X s x) {a b : CatCrypt.Nominal.Atom} (ha : a ∉ s) (hb : b ∉ s) :
    X.ρ (FinPerm.swap a b) x = x := by
  apply hs
  intro e he
  have ea : e ≠ a := fun h => ha (h ▸ he)
  have eb : e ≠ b := fun h => hb (h ▸ he)
  exact FinPerm.swap_apply_of_ne_of_ne ea eb

/-! ## Step 1 — finite supports are closed under intersection (`FinPerm` side)

The port of `Nominal.supports_erase` / `Nominal.supports_inter` from the full-`PermAtom`
development in `NominalMonoidal`, replacing `Equiv.swap` by `FinPerm.swap`, the full permutation
group by `FinPerm`, and the fresh atom `Infinite.exists_notMem_finset` by `Atom.fresh`. -/

/-- **Erase step** for the intersection theorem (`FinPerm` side): if `s` and `t` both support `x`
and `a ∈ s`, `a ∉ t`, then `x` is already supported by `s.erase a`. The single-atom fresh-renaming
move. -/
lemma supportsFin_erase {X : GSetFin} {s t : Finset CatCrypt.Nominal.Atom} {x : X.V}
    (hs : SupportsFin X s x) (ht : SupportsFin X t x) {a : CatCrypt.Nominal.Atom}
    (has : a ∈ s) (hat : a ∉ t) :
    SupportsFin X (s.erase a) x := by
  intro π hπ
  set a' := π a with ha'def
  by_cases haa' : a' = a
  · -- `π` fixes all of `s`, so `SupportsFin X s x` applies directly.
    apply hs
    intro e he
    by_cases hea : e = a
    · subst hea; rw [← ha'def]; exact haa'
    · exact hπ e (Finset.mem_erase.mpr ⟨hea, he⟩)
  · -- `a' = π a ≠ a`. First, `a' ∉ s` by injectivity of `π` on `s.erase a`.
    have ha'ns : a' ∉ s := by
      intro ha's
      have hmem : a' ∈ s.erase a := Finset.mem_erase.mpr ⟨haa', ha's⟩
      have hfix : π a' = a' := hπ a' hmem
      have hpp : π a = π a' := by rw [← ha'def, hfix]
      have heq : a = a' := π.val.injective (by simpa only [FinPerm.apply_def] using hpp)
      exact haa' heq.symm
    -- `ζ := swap a a' * π` fixes `s`, so `ζ • x = x`; hence `π • x = swap a a' • x`.
    have hzeta : X.ρ (FinPerm.swap a a' * π) x = x := by
      apply hs
      intro e he
      rw [FinPerm.mul_apply]
      by_cases hea : e = a
      · subst hea; rw [← ha'def, FinPerm.swap_apply_right]
      · have hpe : π e = e := hπ e (Finset.mem_erase.mpr ⟨hea, he⟩)
        rw [hpe]
        have hea' : e ≠ a' := fun h => ha'ns (h ▸ he)
        exact FinPerm.swap_apply_of_ne_of_ne hea hea'
    have hinv : ∀ y : X.V, X.ρ (FinPerm.swap a a') (X.ρ (FinPerm.swap a a') y) = y := by
      intro y
      rw [← GSetFin.act_mul, FinPerm.swap_swap, GSetFin.act_one]
    have hStepA : X.ρ π x = X.ρ (FinPerm.swap a a') x := by
      have h0 : X.ρ (FinPerm.swap a a') (X.ρ π x) = x := by
        rw [← GSetFin.act_mul]; exact hzeta
      have hkey := hinv (X.ρ π x)
      rw [h0] at hkey
      exact hkey.symm
    -- Fresh atom `c` outside `s ∪ t ∪ {a, a'}` breaks `swap a a'` into two support-fixing swaps.
    obtain ⟨c, hc⟩ : ∃ c : CatCrypt.Nominal.Atom, c ∉ (s ∪ t ∪ {a, a'}) :=
      ⟨CatCrypt.Nominal.Atom.fresh (s ∪ t ∪ {a, a'}),
        CatCrypt.Nominal.Atom.fresh_not_mem _⟩
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨⟨hcs, hct⟩, hca, hca'⟩ := hc
    have hid : FinPerm.swap a a'
        = FinPerm.swap a c * FinPerm.swap a' c * FinPerm.swap a c := by
      apply FinPerm.val_injective
      simp only [FinPerm.mul_val, FinPerm.swap_val]
      have h := Equiv.swap_mul_swap_mul_swap (Ne.symm hca') haa'
      rw [Equiv.swap_comm c a] at h
      exact h.symm
    have hswap : X.ρ (FinPerm.swap a a') x = x := by
      rw [hid, GSetFin.act_mul, GSetFin.act_mul,
        swapFin_apply_eq_self ht hat hct,
        swapFin_apply_eq_self hs ha'ns hcs,
        swapFin_apply_eq_self ht hat hct]
    rw [hStepA, hswap]

/-- Auxiliary for `supportsFin_inter`: strong induction on `(s \ t).card`. -/
private lemma supportsFin_inter_aux {X : GSetFin} {t : Finset CatCrypt.Nominal.Atom} {x : X.V}
    (ht : SupportsFin X t x) :
    ∀ (n : ℕ) (s : Finset CatCrypt.Nominal.Atom), (s \ t).card = n →
      SupportsFin X s x → SupportsFin X (s ∩ t) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro s hcard hs
    rcases Finset.eq_empty_or_nonempty (s \ t) with hemp | ⟨a, ha⟩
    · rw [Finset.sdiff_eq_empty_iff_subset] at hemp
      rwa [Finset.inter_eq_left.mpr hemp]
    · rw [Finset.mem_sdiff] at ha
      obtain ⟨has, hat⟩ := ha
      have hstep : SupportsFin X (s.erase a) x := supportsFin_erase hs ht has hat
      have hset : (s.erase a) \ t = (s \ t).erase a := by
        ext y; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
      have hlt : ((s.erase a) \ t).card < n := by
        rw [hset, ← hcard]
        exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨has, hat⟩)
      have hrec := IH _ hlt (s.erase a) rfl hstep
      have heq : (s.erase a) ∩ t = s ∩ t := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hys⟩, hyt⟩; exact ⟨hys, hyt⟩
        · rintro ⟨hys, hyt⟩
          exact ⟨⟨fun h => hat (h ▸ hyt), hys⟩, hyt⟩
      rwa [heq] at hrec

/-- **Finite `SupportsFin`-supports are closed under intersection.** The classical least-support
result over the finitely-supported permutation group `FinPerm`; the crux unblocking essential
surjectivity of `res`. -/
lemma supportsFin_inter {X : GSetFin} {s t : Finset CatCrypt.Nominal.Atom} {x : X.V}
    (hs : SupportsFin X s x) (ht : SupportsFin X t x) :
    SupportsFin X (s ∩ t) x :=
  supportsFin_inter_aux ht _ s rfl hs

/-! ## Step 2 — the canonical least support on `NomFin` objects -/

/-- The **least support** of an element of a finitely-supported `FinPerm`-set: the intersection of
all supporting finite sets (realized as the `inf'` of the supporting subsets of one chosen
support). -/
noncomputable def suppFin {X : GSetFin} (hX : IsNominalFin X) (x : X.V) :
    Finset CatCrypt.Nominal.Atom :=
  ((hX x).choose.powerset.filter (fun s => SupportsFin X s x)).inf'
    ⟨(hX x).choose,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), (hX x).choose_spec⟩⟩ id

/-- The least support is a support. -/
lemma suppFin_supports {X : GSetFin} (hX : IsNominalFin X) (x : X.V) :
    SupportsFin X (suppFin hX x) x := by
  unfold suppFin
  refine Finset.inf'_induction (p := fun r : Finset CatCrypt.Nominal.Atom => SupportsFin X r x)
    _ id ?_ ?_
  · intro a₁ h₁ a₂ h₂
    exact supportsFin_inter h₁ h₂
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

/-- The least support is contained in every support. -/
lemma suppFin_le {X : GSetFin} (hX : IsNominalFin X) {x : X.V} {s : Finset CatCrypt.Nominal.Atom}
    (hsupp : SupportsFin X s x) : suppFin hX x ⊆ s := by
  have hs0 : SupportsFin X (hX x).choose x := (hX x).choose_spec
  have hmem : s ∩ (hX x).choose ∈
      (hX x).choose.powerset.filter (fun u => SupportsFin X u x) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, supportsFin_inter hsupp hs0⟩
  have hle : suppFin hX x ⊆ s ∩ (hX x).choose := Finset.inf'_le (f := id) hmem
  exact hle.trans Finset.inter_subset_left

/-- Equivariance of `SupportsFin`: if `s` supports `x` then `s.image τ` supports `X.ρ τ x`. The
`FinPerm`-side mirror of `Nominal.Supports.smul`. -/
lemma SupportsFin.smul {X : GSetFin} {s : Finset CatCrypt.Nominal.Atom} {x : X.V}
    (h : SupportsFin X s x) (τ : FinPerm) :
    SupportsFin X (s.image (τ ·)) (X.ρ τ x) := by
  intro σ hσ
  have key : ∀ a ∈ s, (τ⁻¹ * σ * τ) a = a := by
    intro a ha
    have hmem : τ a ∈ s.image (τ ·) := Finset.mem_image_of_mem _ ha
    have hfix : σ (τ a) = τ a := hσ (τ a) hmem
    simp only [FinPerm.mul_apply, hfix]
    rw [← FinPerm.mul_apply, inv_mul_cancel, FinPerm.one_apply]
  have hx : X.ρ (τ⁻¹ * σ * τ) x = x := h _ key
  have e : σ * τ = τ * (τ⁻¹ * σ * τ) := by group
  calc X.ρ σ (X.ρ τ x) = X.ρ (σ * τ) x := (GSetFin.act_mul X σ τ x).symm
    _ = X.ρ (τ * (τ⁻¹ * σ * τ)) x := by rw [e]
    _ = X.ρ τ (X.ρ (τ⁻¹ * σ * τ) x) := GSetFin.act_mul X _ _ x
    _ = X.ρ τ x := by rw [hx]

/-- Supports transport forward along a `FinPerm`-equivariant map. The mirror of
`Nominal.Supports.map`. -/
lemma SupportsFin.map {X Y : GSetFin} (f : X ⟶ Y) {s : Finset CatCrypt.Nominal.Atom} {a : X.V}
    (h : SupportsFin X s a) : SupportsFin Y s (f.hom a) := by
  intro τ hτ
  have hc : f.hom (X.ρ τ a) = Y.ρ τ (f.hom a) := congrFun (f.comm τ) a
  rw [← hc, h τ hτ]

/-- **The least support is equivariant** (`suppFin (X.ρ τ x) = (suppFin x).image τ`), which is
exactly the datum `extObj` requires. Least supports are always equivariant. -/
lemma suppFin_equivariant {X : GSetFin} (hX : IsNominalFin X) (x : X.V) (τ : FinPerm) :
    suppFin hX (X.ρ τ x) = (suppFin hX x).image (τ ·) := by
  apply Finset.Subset.antisymm
  · exact suppFin_le hX ((suppFin_supports hX x).smul τ)
  · have hxx : X.ρ τ⁻¹ (X.ρ τ x) = x := by
      rw [← GSetFin.act_mul, inv_mul_cancel, GSetFin.act_one]
    have hback : suppFin hX x ⊆ (suppFin hX (X.ρ τ x)).image (τ⁻¹ ·) := by
      have h1 := suppFin_le hX ((suppFin_supports hX (X.ρ τ x)).smul τ⁻¹)
      rwa [hxx] at h1
    have hcollapse : ((suppFin hX (X.ρ τ x)).image (τ⁻¹ ·)).image (τ ·)
        = suppFin hX (X.ρ τ x) := by
      rw [Finset.image_image]
      have hfun : ((τ ·) ∘ (τ⁻¹ ·)) = (id : CatCrypt.Nominal.Atom → CatCrypt.Nominal.Atom) := by
        funext b
        show τ (τ⁻¹ b) = b
        rw [← FinPerm.mul_apply, mul_inv_cancel, FinPerm.one_apply]
      rw [hfun, Finset.image_id]
    calc (suppFin hX x).image (τ ·)
        ⊆ ((suppFin hX (X.ρ τ x)).image (τ⁻¹ ·)).image (τ ·) :=
          Finset.image_subset_image hback
      _ = suppFin hX (X.ρ τ x) := hcollapse

/-! ## Step 3 — the extension functor `extFunctor : NomFin ⥤ Nom` -/

/-- The object-level extension of an *arbitrary* `NomFin` object, using its canonical least
support `suppFin`. -/
noncomputable def extObjFin (X : NomFin) : Nom :=
  extObj X.obj (suppFin X.property) (fun x => suppFin_supports X.property x)
    (fun x τ => suppFin_equivariant X.property x τ)

/-- The extension functor `NomFin ⥤ Nom`: on objects it reconstructs the full-`PermAtom` action
from the canonical least support; on a `FinPerm`-equivariant morphism it keeps the same underlying
function, now `PermAtom`-equivariant for the reconstructed actions. -/
noncomputable def extFunctor : NomFin ⥤ Nom where
  obj X := extObjFin X
  map {X Y} f :=
    ObjectProperty.homMk
      { hom := f.hom.hom
        comm := by
          intro π
          funext x
          show f.hom.hom (X.obj.ρ (extendPerm (fromPermℕ π) (suppFin X.property x)) x)
              = Y.obj.ρ (extendPerm (fromPermℕ π) (suppFin Y.property (f.hom.hom x))) (f.hom.hom x)
          have hcomm : f.hom.hom (X.obj.ρ (extendPerm (fromPermℕ π) (suppFin X.property x)) x)
              = Y.obj.ρ (extendPerm (fromPermℕ π) (suppFin X.property x)) (f.hom.hom x) :=
            congrFun (f.hom.comm (extendPerm (fromPermℕ π) (suppFin X.property x))) x
          rw [hcomm]
          refine actFin_eq_of_agree (suppFin_supports Y.property (f.hom.hom x)) ?_
          intro a ha
          have hsub : suppFin Y.property (f.hom.hom x) ⊆ suppFin X.property x :=
            suppFin_le Y.property ((suppFin_supports X.property x).map f.hom)
          rw [extendPerm_spec _ _ a (hsub ha), extendPerm_spec _ _ a ha] }
  map_id X := by
    apply ObjectProperty.hom_ext; apply Action.Hom.ext; rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext; apply Action.Hom.ext; rfl

/-! ## Step 4 — the round-trip `ext ∘ res ≅ 𝟭` on `Nom`

For `A : Nom`, extending the restricted `FinPerm`-action recovers the original full-`PermAtom`
action, because a `FinPerm`-support of `x` (transported by `coreAtomEquiv`) is a genuine
full-`PermAtom` support of `x` in `A` (`supports_of_supportsFin_res`). -/

/-- A `FinPerm`-support for the restricted action of a nominal `A`, transported along
`coreAtomEquiv`, is a full-`PermAtom` support of the same element in `A`. -/
lemma supports_of_supportsFin_res {A : GSet} (hA : IsNominal A)
    {s : Finset CatCrypt.Nominal.Atom} {x : A.V}
    (h : SupportsFin (resGSet.obj A) s x) :
    Supports A (s.image coreAtomEquiv) x := by
  intro π hπ
  obtain ⟨sA, hsA⟩ := hA x
  have hτfix : ∀ b ∈ s,
      extendPerm (fromPermℕ π) (s ∪ sA.image coreAtomEquiv.symm) b = b := by
    intro b hb
    have hb' : b ∈ s ∪ sA.image coreAtomEquiv.symm := Finset.mem_union_left _ hb
    have hmem : coreAtomEquiv b ∈ s.image coreAtomEquiv := Finset.mem_image_of_mem _ hb
    have hπb := hπ (coreAtomEquiv b) hmem
    rw [extendPerm_spec (fromPermℕ π) _ b hb']
    simp [fromPermℕ, Equiv.permCongr_apply, hπb]
  have hfixres :
      A.ρ (finPermToPerm (extendPerm (fromPermℕ π) (s ∪ sA.image coreAtomEquiv.symm))) x = x :=
    h (extendPerm (fromPermℕ π) (s ∪ sA.image coreAtomEquiv.symm)) hτfix
  have hagree : ∀ n ∈ sA,
      finPermToPerm (extendPerm (fromPermℕ π) (s ∪ sA.image coreAtomEquiv.symm)) n = π n := by
    intro n hn
    have hpre : coreAtomEquiv.symm n ∈ s ∪ sA.image coreAtomEquiv.symm :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hn)
    have hτn' : (extendPerm (fromPermℕ π) (s ∪ sA.image coreAtomEquiv.symm)).val
        (coreAtomEquiv.symm n) = fromPermℕ π (coreAtomEquiv.symm n) :=
      extendPerm_spec (fromPermℕ π) _ (coreAtomEquiv.symm n) hpre
    simp only [finPermToPerm, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.permCongr_apply]
    rw [hτn']
    simp only [fromPermℕ, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [act_eq_of_supports hsA hagree] at hfixres
  exact hfixres

/-- **The round-trip `ext ∘ res ≅ 𝟭`** on `Nom`: extending the restricted action of `A : Nom`
recovers `A`. Underlying-iso is the identity on the shared carrier; compatibility follows because
the reconstructed action agrees with the original on the (transported) least support. -/
noncomputable def extResGSetIso (A : Nom) :
    (extObjFin (res.obj A)).obj ≅ A.obj :=
  Action.mkIso (Iso.refl _)
    (by
      intro π
      funext x
      simp only [Iso.refl_hom, types_id_apply, types_comp_apply]
      show A.obj.ρ (finPermToPerm
          (extendPerm (fromPermℕ π) (suppFin (res.obj A).property x))) x = A.obj.ρ π x
      have hsupp :
          Supports A.obj ((suppFin (res.obj A).property x).image coreAtomEquiv) x :=
        supports_of_supportsFin_res A.property (suppFin_supports (res.obj A).property x)
      refine act_eq_of_supports hsupp ?_
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨b, hb, rfl⟩ := hn
      have hτb : (extendPerm (fromPermℕ π) (suppFin (res.obj A).property x)).val b
          = fromPermℕ π b :=
        extendPerm_spec (fromPermℕ π) (suppFin (res.obj A).property x) b hb
      simp only [finPermToPerm, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.permCongr_apply,
        Equiv.symm_apply_apply]
      rw [hτb]
      simp only [fromPermℕ, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply])

/-- The round-trip `ext ∘ res ≅ 𝟭` as an isomorphism of `Nom` objects. -/
noncomputable def extResIso (A : Nom) : extFunctor.obj (res.obj A) ≅ A :=
  ObjectProperty.isoMk _ (extResGSetIso A)

/-! ## Step 5 — the equivalence `NomFin ≌ Nom` -/

/-- `res` is essentially surjective: every `NomFin` object is `res.obj` of its extension, via the
round-trip iso `resExtIso`. Together with fullness and faithfulness this makes `res` an
equivalence. -/
noncomputable instance instEssSurjRes : res.EssSurj where
  mem_essImage Y :=
    ⟨extObjFin Y,
      ⟨resExtIso Y.obj (suppFin Y.property) (fun x => suppFin_supports Y.property x)
        (fun x τ => suppFin_equivariant Y.property x τ)⟩⟩

/-- `res : Nom ⥤ NomFin` is an equivalence of categories (full + faithful + essentially
surjective). -/
noncomputable instance instIsEquivalenceRes : res.IsEquivalence where

/-- **The Schanuel identification, at full categorical strength:** the category of finitely
supported `FinPerm`-sets (core nominal sets) is equivalent to the category `Nom` of nominal sets
for the full permutation group. -/
noncomputable def nomFinEquivNom : NomFin ≌ Nom :=
  res.asEquivalence.symm

end Nominal
