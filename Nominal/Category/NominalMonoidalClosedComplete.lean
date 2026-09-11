/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Nominal.Category.NominalSeparatedExp

set_option autoImplicit false

/-!
# M3, part 4 — the totalized transpose `curryQ` and `MonoidalClosed Nom`

`CatCrypt.Category.NominalSeparatedExp` built the separated exponential `B ⊸ₛ C` (the
fresh-agreement quotient of the finitely-supported function space) and proved that the transpose

  `uncurryQ : (A ⟶ B ⊸ₛ C) → (A ⊗ₙ B ⟶ C)`

is **injective** (`uncurryQ_injective`).  The only missing datum for the closed structure is the
inverse transpose — a *finitely-supported totalization* of the fresh-value assignment
`b ↦ g ⟨(a, b), _⟩`.

## Scope

* **`curryFn` / `curryElt`** — the totalization.  For `g : A ⊗ₙ B ⟶ C` and `a : A.obj.V` we extend
  the fresh values `b ↦ g ⟨(a, b), _⟩` (defined on the separated locus) to a *total* finitely
  supported function by a single constant default off the fresh locus.  The default's value is
  irrelevant to the fresh-agreement class (it is quotiented away); the extension is finitely
  supported, which is all `funCarrier` requires.
* **`curryFn_sep`** — the extension agrees with `g` on the separated locus (β on the fresh part).
* **`curryQ`** — `a ↦ ⟦curryFn g a⟧`, an equivariant `Nom`-morphism `A ⟶ B ⊸ₛ C`.
* **round-trips** `uncurryQ (curryQ g) = g` and `curryQ (uncurryQ h) = h` (the second via
  `uncurryQ_injective`).
* **`instance : MonoidalClosed Nom`** — assembled from the transpose bijection.

The technique throughout is the *fresh-renaming reduction* already used in
`freshAgree_trans`/`uncurryQ_injective`: any fresh-agreement obligation at an arbitrary argument
`b` is transported by a support-fixing permutation to a *fully separated* argument, where both
sides collapse to `g`-values and agree by `curry_sep_transport`.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

@[expose] public section

open CategoryTheory

open scoped Classical

namespace Nominal

variable {A B C : Nom}

/-! ## Fresh-renaming helpers -/

/-- If `π` fixes `s` pointwise then so does `π⁻¹`. -/
lemma perm_inv_fix {s : Finset Atom} {π : PermAtom} (hπ : ∀ a ∈ s, π a = a) :
    ∀ a ∈ s, π⁻¹ a = a := by
  intro a ha
  have h := hπ a ha
  conv_lhs => rw [← h]
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

/-- Separation is preserved (in both directions) by a permutation fixing `supp a`. -/
lemma sep_smul_of_fix {a : A.obj.V} {b : B.obj.V} {π : PermAtom}
    (hπ : ∀ x ∈ supp A.property a, π x = x)
    (h : Separated A.obj B.obj a b) : Separated A.obj B.obj a (B.obj.act π b) := by
  have ha : A.obj.act π a = a := supp_supports A.property a π hπ
  have hs := h.smul π
  rwa [ha] at hs

/-- The separation-preservation of `sep_smul_of_fix` as an iff. -/
lemma sep_smul_iff_of_fix {a : A.obj.V} {b : B.obj.V} {π : PermAtom}
    (hπ : ∀ x ∈ supp A.property a, π x = x) :
    Separated A.obj B.obj a (B.obj.act π b) ↔ Separated A.obj B.obj a b := by
  constructor
  · intro h
    have hinv := sep_smul_of_fix (A := A) (B := B) (π := π⁻¹) (perm_inv_fix hπ) h
    rwa [← GSet.act_mul, inv_mul_cancel, GSet.act_one] at hinv
  · exact sep_smul_of_fix hπ

/-- A permutation carrying `supp b` off `supp a` (fixing nothing in particular). -/
noncomputable def freshenPerm (a : A.obj.V) (b : B.obj.V) : PermAtom :=
  (exists_avoiding_perm (∅ : Finset Atom) (supp A.property a) (supp B.property b)
    (Finset.disjoint_empty_right _)).choose

/-- After `freshenPerm`, the point is separated from `a`. -/
lemma freshenPerm_sep (a : A.obj.V) (b : B.obj.V) :
    Separated A.obj B.obj a (B.obj.act (freshenPerm a b) b) := by
  have hspec := (exists_avoiding_perm (∅ : Finset Atom) (supp A.property a) (supp B.property b)
    (Finset.disjoint_empty_right _)).choose_spec
  rw [Separated_iff_disjoint A.property B.property, supp_smul B.property (freshenPerm a b) b,
    Finset.disjoint_left]
  intro y hy hy2
  rw [Finset.mem_image] at hy2
  obtain ⟨x, hx, rfl⟩ := hy2
  exact hspec.2 x hx hy

/-! ## The totalization -/

/-- A constant default `C`-value used off the separated locus.  Its precise value is irrelevant to
the fresh-agreement class of `curryFn`. -/
noncomputable def curryDflt (g : A ⊗ₙ B ⟶ C) (a : A.obj.V) (hB : Nonempty B.obj.V) : C.obj.V :=
  g.hom.hom ⟨(a, B.obj.act (freshenPerm a hB.some) hB.some), freshenPerm_sep a hB.some⟩

/-- **The finitely-supported totalization** of the fresh-value assignment `b ↦ g ⟨(a, b), _⟩`.
On the separated locus it is `g`; off it, the constant default. -/
noncomputable def curryFn (g : A ⊗ₙ B ⟶ C) (a : A.obj.V) : B.obj.V → C.obj.V :=
  fun b => if hB : Nonempty B.obj.V then
    (if hsep : Separated A.obj B.obj a b then g.hom.hom ⟨(a, b), hsep⟩ else curryDflt g a hB)
  else absurd (⟨b⟩ : Nonempty B.obj.V) hB

/-- `curryFn` on the separated locus is `g`. -/
lemma curryFn_sep (g : A ⊗ₙ B ⟶ C) (a : A.obj.V) {b : B.obj.V}
    (hsep : Separated A.obj B.obj a b) :
    curryFn g a b = g.hom.hom ⟨(a, b), hsep⟩ := by
  have hB : Nonempty B.obj.V := ⟨b⟩
  simp only [curryFn, dif_pos hB, dif_pos hsep]

/-- `curryFn` off the separated locus is the constant default. -/
lemma curryFn_dflt (g : A ⊗ₙ B ⟶ C) (a : A.obj.V) {b : B.obj.V}
    (hB : Nonempty B.obj.V) (hsep : ¬ Separated A.obj B.obj a b) :
    curryFn g a b = curryDflt g a hB := by
  simp only [curryFn, dif_pos hB, dif_neg hsep]

/-- `curryFn g a` is finitely supported. -/
lemma curryFn_hasFinSupp (g : A ⊗ₙ B ⟶ C) (a : A.obj.V) :
    HasFinSupport (funGSetFull B.obj C.obj) (curryFn g a) := by
  by_cases hB : Nonempty B.obj.V
  · refine ⟨supp A.property a ∪ supp C.property (curryDflt g a hB), ?_⟩
    intro π hπ
    have hπa : ∀ x ∈ supp A.property a, π x = x :=
      fun x hx => hπ x (Finset.mem_union_left _ hx)
    have hπd : ∀ x ∈ supp C.property (curryDflt g a hB), π x = x :=
      fun x hx => hπ x (Finset.mem_union_right _ hx)
    funext b
    show C.obj.act π (curryFn g a (B.obj.act π⁻¹ b)) = curryFn g a b
    by_cases hsep : Separated A.obj B.obj a b
    · have hsep' : Separated A.obj B.obj a (B.obj.act π⁻¹ b) :=
        (sep_smul_iff_of_fix (perm_inv_fix hπa)).mpr hsep
      rw [curryFn_sep g a hsep', curryFn_sep g a hsep]
      have hb : B.obj.act π (B.obj.act π⁻¹ b) = b := by
        rw [← GSet.act_mul, mul_inv_cancel, GSet.act_one]
      have key := curry_sep_transport g a hπa hsep'
        (show Separated A.obj B.obj a (B.obj.act π (B.obj.act π⁻¹ b)) by rw [hb]; exact hsep)
      rw [← key]
      exact congrArg g.hom.hom (Subtype.ext (congrArg (Prod.mk a) hb))
    · have hsep' : ¬ Separated A.obj B.obj a (B.obj.act π⁻¹ b) := by
        intro h
        exact hsep ((sep_smul_iff_of_fix (perm_inv_fix hπa)).mp h)
      rw [curryFn_dflt g a hB hsep', curryFn_dflt g a hB hsep]
      exact supp_supports C.property (curryDflt g a hB) π hπd
  · refine ⟨∅, ?_⟩
    intro π _
    funext b
    exact absurd (⟨b⟩ : Nonempty B.obj.V) hB

/-- The totalization packaged as an element of the internal-hom carrier `funCarrier B.obj C.obj`. -/
noncomputable def curryElt (g : A ⊗ₙ B ⟶ C) (a : A.obj.V) : funCarrier B.obj C.obj :=
  ⟨curryFn g a, curryFn_hasFinSupp g a⟩

@[simp] lemma curryElt_coe (g : A ⊗ₙ B ⟶ C) (a : A.obj.V) :
    (curryElt g a).1 = curryFn g a := rfl

/-! ## The fresh-renaming reduction

To prove a fresh-agreement between two finitely-supported functions it suffices to prove they agree
on the locus separated from a *fixed* finite set `s`: an arbitrary fresh-agreement argument is
transported by a support-fixing renaming to that separated locus, and the values transport back by
the conjugation equivariance. -/

/-- **Fresh-locus suffices for fresh agreement.**  If `f₁` and `f₂` agree at every `b` separated
from a fixed `s`, they fresh-agree. -/
lemma freshAgree_of_fresh_eq {f₁ f₂ : funCarrier B.obj C.obj} {s : Finset Atom}
    (hval : ∀ b : B.obj.V, Disjoint s (supp B.property b) → f₁.1 b = f₂.1 b) :
    freshAgree B C f₁ f₂ := by
  intro b hb
  obtain ⟨π, hπfix, hπav⟩ :=
    exists_avoiding_perm (fsupp B C f₁ ∪ fsupp B C f₂) (fsupp B C f₁ ∪ fsupp B C f₂ ∪ s)
      (supp B.property b) hb.symm
  set b' := B.obj.act π b with hb'
  have hSf₁ : Supports (funGSetFull B.obj C.obj) (fsupp B C f₁) f₁.1 :=
    funGSet_supports_val (fsupp_supports B C f₁)
  have hSf₂ : Supports (funGSetFull B.obj C.obj) (fsupp B C f₂) f₂.1 :=
    funGSet_supports_val (fsupp_supports B C f₂)
  have hπ1 : ∀ x ∈ fsupp B C f₁, π x = x := fun x hx => hπfix x (Finset.mem_union_left _ hx)
  have hπ2 : ∀ x ∈ fsupp B C f₂, π x = x := fun x hx => hπfix x (Finset.mem_union_right _ hx)
  have e1 : f₁.1 b' = C.obj.act π (f₁.1 b) := funGSetFull_apply_of_supports hSf₁ hπ1 b
  have e2 : f₂.1 b' = C.obj.act π (f₂.1 b) := funGSetFull_apply_of_supports hSf₂ hπ2 b
  have hb'sep : Disjoint s (supp B.property b') := by
    rw [hb', supp_smul B.property π b, Finset.disjoint_left]
    intro y hy hy2
    rw [Finset.mem_image] at hy2
    obtain ⟨x, hx, rfl⟩ := hy2
    exact hπav x hx (Finset.mem_union_right _ hy)
  have hval' := hval b' hb'sep
  rw [e1, e2] at hval'
  have hc := congrArg (C.obj.act π⁻¹) hval'
  rwa [← GSet.act_mul, ← GSet.act_mul, inv_mul_cancel, GSet.act_one, GSet.act_one] at hc

/-! ## `curryQ` -/

/-- **Class support.**  The class `⟦curryElt g a⟧` is supported by `supp a`. -/
lemma curryElt_class_supp (g : A ⊗ₙ B ⟶ C) (a : A.obj.V) :
    Supports (sepExpGSet B C) (supp A.property a)
      (Quotient.mk (freshAgreeSetoid B C) (curryElt g a)) := by
  intro π hπ
  rw [sepExpGSet_ρ_mk]
  apply Quotient.sound
  refine freshAgree_of_fresh_eq (s := supp A.property a) ?_
  intro b hbs
  have hsep : Separated A.obj B.obj a b :=
    (Separated_iff_disjoint A.property B.property a b).mpr hbs
  have hsep' : Separated A.obj B.obj a (B.obj.act π⁻¹ b) :=
    (sep_smul_iff_of_fix (perm_inv_fix hπ)).mpr hsep
  show ((funGSet B.obj C.obj).act π (curryElt g a)).1 b = (curryElt g a).1 b
  rw [funGSet_ρ_coe, funGSetFull_ρ, curryElt_coe, curryFn_sep g a hsep', curryFn_sep g a hsep]
  have hb : B.obj.act π (B.obj.act π⁻¹ b) = b := by
    rw [← GSet.act_mul, mul_inv_cancel, GSet.act_one]
  have key := curry_sep_transport g a hπ hsep'
    (show Separated A.obj B.obj a (B.obj.act π (B.obj.act π⁻¹ b)) by rw [hb]; exact hsep)
  rw [← key]
  exact congrArg g.hom.hom (Subtype.ext (congrArg (Prod.mk a) hb))

/-- Underlying equivariant map of the quotient currying `A ⟶ B ⊸ₛ C`. -/
noncomputable def curryQActionHom (g : A ⊗ₙ B ⟶ C) : A.obj ⟶ (B ⊸ₛ C).obj where
  hom := TypeCat.ofHom fun a => Quotient.mk (freshAgreeSetoid B C) (curryElt g a)
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro a
    show Quotient.mk (freshAgreeSetoid B C) (curryElt g (A.obj.act π a))
      = (sepExpGSet B C).act π (Quotient.mk (freshAgreeSetoid B C) (curryElt g a))
    rw [sepExpGSet_ρ_mk]
    apply Quotient.sound
    refine freshAgree_of_fresh_eq (s := supp A.property (A.obj.act π a)) ?_
    intro b hbs
    -- `b` is separated from `a' = A.act π a`; hence `B.act π⁻¹ b` is separated from `a`.
    have hsepa' : Separated A.obj B.obj (A.obj.act π a) b :=
      (Separated_iff_disjoint A.property B.property _ b).mpr hbs
    have hdisj_a : Disjoint (supp A.property a) (supp B.property (B.obj.act π⁻¹ b)) := by
      rw [supp_smul B.property π⁻¹ b]
      have hb2 : Disjoint ((supp A.property a).image π) (supp B.property b) := by
        rw [← supp_smul A.property π a]; exact hbs
      exact disjoint_image_perm hb2
    have hsepa : Separated A.obj B.obj a (B.obj.act π⁻¹ b) :=
      (Separated_iff_disjoint A.property B.property a _).mpr hdisj_a
    show (curryElt g (A.obj.act π a)).1 b = ((funGSet B.obj C.obj).act π (curryElt g a)).1 b
    rw [funGSet_ρ_coe, funGSetFull_ρ, curryElt_coe, curryElt_coe,
      curryFn_sep g (A.obj.act π a) hsepa', curryFn_sep g a hsepa]
    -- g's equivariance: `g (π · ⟨(a, π⁻¹ b)⟩) = C.act π (g ⟨(a, π⁻¹ b)⟩)`
    have hc : g.hom.hom ((sepGSet A.obj B.obj).act π ⟨(a, B.obj.act π⁻¹ b), hsepa⟩)
        = C.obj.act π (g.hom.hom ⟨(a, B.obj.act π⁻¹ b), hsepa⟩) := by
      have := ConcreteCategory.congr_hom (g.hom.comm π)
        (⟨(a, B.obj.act π⁻¹ b), hsepa⟩ : sepCarrier A.obj B.obj)
      simpa only [ConcreteCategory.comp_apply] using! this
    have hb : B.obj.act π (B.obj.act π⁻¹ b) = b := by
      rw [← GSet.act_mul, mul_inv_cancel, GSet.act_one]
    have hpair : (sepGSet A.obj B.obj).act π ⟨(a, B.obj.act π⁻¹ b), hsepa⟩
        = (⟨(A.obj.act π a, b), hsepa'⟩ : sepCarrier A.obj B.obj) :=
      Subtype.ext (by
        show (A.obj.act π a, B.obj.act π (B.obj.act π⁻¹ b)) = (A.obj.act π a, b); rw [hb])
    rw [hpair] at hc
    exact hc

/-- **Quotient currying**: transpose `A ⊗ₙ B ⟶ C` to `A ⟶ B ⊸ₛ C`. -/
noncomputable def curryQ (g : A ⊗ₙ B ⟶ C) : A ⟶ B ⊸ₛ C :=
  ObjectProperty.homMk (curryQActionHom g)

@[simp] lemma curryQ_hom_hom (g : A ⊗ₙ B ⟶ C) (a : A.obj.V) :
    (curryQ g).hom.hom a = Quotient.mk (freshAgreeSetoid B C) (curryElt g a) := rfl

/-! ## Round-trips -/

/-- **β-rule for the quotient transpose.**  On a separated pair, `uncurryQ (curryQ g)` is `g`. -/
theorem uncurryQ_curryQ (g : A ⊗ₙ B ⟶ C) : uncurryQ (curryQ g) = g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext; intro p
  obtain ⟨⟨a, b⟩, hsep⟩ := p
  show evalCls B C ((curryQ g).hom.hom a) b _ = g.hom.hom ⟨(a, b), hsep⟩
  have hab : Disjoint (supp A.property a) (supp B.property b) :=
    (Separated_iff_disjoint A.property B.property a b).mp hsep
  -- an explicit fresh representative of `⟦curryElt g a⟧`
  obtain ⟨σ, hσfix, hσav⟩ :=
    exists_avoiding_perm (supp A.property a) (supp B.property b)
      (fsupp B C (curryElt g a) \ supp A.property a) Finset.sdiff_disjoint
  set g' := (funGSet B.obj C.obj).act σ (curryElt g a) with hg'def
  have hgX : Quotient.mk (freshAgreeSetoid B C) g' = (curryQ g).hom.hom a := by
    rw [curryQ_hom_hom]
    have h := curryElt_class_supp g a σ hσfix
    rwa [sepExpGSet_ρ_mk] at h
  have hgb : Disjoint (fsupp B C g') (supp B.property b) := by
    rw [hg'def, fsupp_smul, Finset.disjoint_left]
    intro y hy hyb
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    by_cases hxa : x ∈ supp A.property a
    · rw [hσfix x hxa] at hyb
      exact Finset.disjoint_left.mp hab hxa hyb
    · exact hσav x (Finset.mem_sdiff.mpr ⟨hx, hxa⟩) hyb
  rw [evalCls_eq B C _ b _ g' hgX hgb]
  -- compute the value of the explicit representative
  have hsepσ' : Separated A.obj B.obj a (B.obj.act σ⁻¹ b) :=
    (sep_smul_iff_of_fix (perm_inv_fix hσfix)).mpr hsep
  show ((funGSet B.obj C.obj).act σ (curryElt g a)).1 b = g.hom.hom ⟨(a, b), hsep⟩
  rw [funGSet_ρ_coe, funGSetFull_ρ, curryElt_coe, curryFn_sep g a hsepσ']
  have hb : B.obj.act σ (B.obj.act σ⁻¹ b) = b := by
    rw [← GSet.act_mul, mul_inv_cancel, GSet.act_one]
  have key := curry_sep_transport g a hσfix hsepσ'
    (show Separated A.obj B.obj a (B.obj.act σ (B.obj.act σ⁻¹ b)) by rw [hb]; exact hsep)
  rw [← key]
  exact congrArg g.hom.hom (Subtype.ext (congrArg (Prod.mk a) hb))

/-- **The inverse round-trip.**  `curryQ (uncurryQ h) = h`, from `uncurryQ_injective` and the β-rule.
-/
theorem curryQ_uncurryQ (h : A ⟶ B ⊸ₛ C) : curryQ (uncurryQ h) = h :=
  uncurryQ_injective (uncurryQ_curryQ (uncurryQ h))

/-! ## The internal-hom functor `B ⊸ₛ -` -/

/-- Postcomposition by an equivariant map preserves fresh agreement. -/
lemma funSepMap_respects {Y Y' : Nom} (k : Y ⟶ Y') {f g : funCarrier B.obj Y.obj}
    (hfg : freshAgree B Y f g) :
    freshAgree B Y' ((funMapActionHom k).hom f) ((funMapActionHom k).hom g) := by
  refine freshAgree_of_fresh_eq (s := fsupp B Y f ∪ fsupp B Y g) ?_
  intro b hbs
  show k.hom.hom (f.1 b) = k.hom.hom (g.1 b)
  rw [hfg b hbs]

/-- Underlying equivariant map of the internal-hom functor on morphisms. -/
noncomputable def funSepMapActionHom {Y Y' : Nom} (k : Y ⟶ Y') :
    sepExpGSet B Y ⟶ sepExpGSet B Y' where
  hom := TypeCat.ofHom (Quotient.lift
    (fun f => Quotient.mk (freshAgreeSetoid B Y') ((funMapActionHom k).hom f))
    (fun _ _ hfg => Quotient.sound (funSepMap_respects k hfg)))
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro X
    induction X using Quotient.inductionOn with
    | _ f =>
      show Quotient.mk (freshAgreeSetoid B Y')
          ((funMapActionHom k).hom ((funGSet B.obj Y.obj).act π f))
        = Quotient.mk (freshAgreeSetoid B Y')
          ((funGSet B.obj Y'.obj).act π ((funMapActionHom k).hom f))
      refine congrArg _ ?_
      have hc := ConcreteCategory.congr_hom ((funMapActionHom k).comm π) f
      simpa only [ConcreteCategory.comp_apply] using! hc

@[simp] lemma funSepMapActionHom_mk {Y Y' : Nom} (k : Y ⟶ Y') (f : funCarrier B.obj Y.obj) :
    (funSepMapActionHom k).hom (Quotient.mk (freshAgreeSetoid B Y) f)
      = Quotient.mk (freshAgreeSetoid B Y') ((funMapActionHom k).hom f) := rfl

/-- The **internal-hom functor** `B ⊸ₛ · : Nom ⥤ Nom` (the right adjoint of `· ⊗ₙ B`). -/
noncomputable def funSepFunctor (B : Nom) : Nom ⥤ Nom where
  obj Y := B ⊸ₛ Y
  map k := ObjectProperty.homMk (funSepMapActionHom k)
  map_id := by
    intro Y
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext; intro X
    induction X using Quotient.inductionOn with
    | _ f => rfl
  map_comp := by
    intro Y Y' Y'' k k'
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext; intro X
    induction X using Quotient.inductionOn with
    | _ f => rfl

@[simp] lemma funSepFunctor_map_mk {Y Y' : Nom} (k : Y ⟶ Y') (f : funCarrier B.obj Y.obj) :
    ((funSepFunctor B).map k).hom.hom (Quotient.mk (freshAgreeSetoid B Y) f)
      = Quotient.mk (freshAgreeSetoid B Y') ((funMapActionHom k).hom f) := rfl

/-! ## Naturality of the transpose in the codomain -/

/-- **Codomain naturality of `uncurryQ`.**  Uncurrying commutes with postcomposition through the
internal-hom functor. -/
lemma uncurryQ_comp_map {X Y Y' : Nom} (h : X ⟶ B ⊸ₛ Y) (g : Y ⟶ Y') :
    uncurryQ (h ≫ (funSepFunctor B).map g) = uncurryQ h ≫ g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext; intro p
  obtain ⟨⟨a, b⟩, hsep⟩ := p
  have hHsupp : Supports (sepExpGSet B Y) (supp X.property a) (h.hom.hom a) :=
    Supports.map h.hom (supp_supports X.property a)
  have hab : Disjoint (supp X.property a) (supp B.property b) :=
    (Separated_iff_disjoint X.property B.property a b).mp hsep
  obtain ⟨f', hf'X, hf'b⟩ := exists_fresh_rep B Y (h.hom.hom a) b hHsupp hab
  show evalCls B Y' ((h ≫ (funSepFunctor B).map g).hom.hom a) b _
      = g.hom.hom (evalCls B Y (h.hom.hom a) b _)
  rw [evalCls_eq B Y (h.hom.hom a) b _ f' hf'X hf'b]
  have hmap : ((funSepFunctor B).map g).hom.hom (h.hom.hom a)
      = Quotient.mk (freshAgreeSetoid B Y') ((funMapActionHom g).hom f') := by
    rw [← hf'X]; rfl
  have hf'b' : Disjoint (fsupp B Y' ((funMapActionHom g).hom f')) (supp B.property b) := by
    have hsub : fsupp B Y' ((funMapActionHom g).hom f') ⊆ fsupp B Y f' :=
      supp_le (funGSet_isNominal B.obj Y'.obj)
        (Supports.map (funMapActionHom g) (fsupp_supports B Y f'))
    exact hf'b.mono_left hsub
  exact evalCls_eq B Y' ((h ≫ (funSepFunctor B).map g).hom.hom a) b _
    ((funMapActionHom g).hom f') hmap.symm hf'b'

/-! ## The adjunction and `MonoidalClosed Nom` -/

/-- The transpose adjunction `· ⊗ₙ B ⊣ (B ⊸ₛ ·)`. -/
noncomputable def tensorRightSepAdj (B : Nom) :
    MonoidalCategory.tensorRight B ⊣ funSepFunctor B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := curryQ
          invFun := uncurryQ
          left_inv := uncurryQ_curryQ
          right_inv := curryQ_uncurryQ }
      homEquiv_naturality_left_symm := by
        intro X' X Y f k
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext; intro p
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        show curryQ (f ≫ g) = curryQ f ≫ (funSepFunctor B).map g
        apply uncurryQ_injective
        rw [uncurryQ_curryQ]
        exact ((uncurryQ_comp_map (curryQ f) g).trans
          (congrArg (· ≫ g) (uncurryQ_curryQ f))).symm }

/-- `tensorLeft B ≅ tensorRight B` from the braiding, natural in the argument. -/
noncomputable def braidNatIso (B : Nom) :
    MonoidalCategory.tensorLeft B ≅ MonoidalCategory.tensorRight B :=
  NatIso.ofComponents (fun A => sepBraiding B A) (by
    intro A A' f
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext; intro p
    rfl)

/-- Every object of `Nom` is closed for the separated product: `· ⊗ₙ B` has the separated
exponential `B ⊸ₛ ·` as right adjoint. -/
noncomputable instance closedNom (B : Nom) : Closed B where
  rightAdj := funSepFunctor B
  adj := (tensorRightSepAdj B).ofNatIsoLeft (braidNatIso B).symm

/-- **`Nom` is symmetric monoidal closed** for the separated product, with internal hom the
fresh-agreement quotient `B ⊸ₛ C`. -/
noncomputable instance monoidalClosedNom : MonoidalClosed Nom where
  closed B := closedNom B

end Nominal
