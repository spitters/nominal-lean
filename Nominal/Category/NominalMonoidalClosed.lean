/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.NominalMonoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

set_option autoImplicit false

/-!
# Toward monoidal closure of `Nom` for the separated product (M3)

This file builds the internal-hom object for the separated-product monoidal structure on `Nom`
established in `CatCrypt.Category.NominalMonoidal`, and develops the currying/uncurrying data of
the intended right adjoint to `· ⊗ₙ B`.

## STEP 1 — the internal-hom object `funGSet`

`funGSet A B` is the nominal set of **finitely supported functions** `A.V → B.V` under the
conjugation action `(π • f) x = B.ρ π (f (A.ρ π⁻¹ x))`.  We prove the conjugation action is a
genuine group action and that the finite-support subtype is nominal, and package it as an object
`funObj B C : Nom`.

## STEP 2 — evaluation and (un)currying

`evalHom : funObj B C ⊗ₙ B ⟶ C` is the evaluation morphism (the counit component), and
`uncurry : (A ⟶ funObj B C) → (A ⊗ₙ B ⟶ C)` transposes a morphism.  Both are genuine equivariant
morphisms of nominal sets, fully proved.

## STEP 3 — the adjunction / `MonoidalClosed Nom`

See the closing section for the precise residual: totalizing `curry` at non-separated arguments
(and the accompanying determined-by-fresh-values extensionality) is the single remaining nominal
prerequisite; it is documented, not registered as a vacuous instance.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

open scoped Classical

namespace Nominal

/-! ## STEP 1 — the internal-hom object -/

/-- The **conjugation `G`-set** on the full function space `A.V → B.V`: `PermAtom` acts by
`(π • f) x = B.ρ π (f (A.ρ π⁻¹ x))`. -/
def funGSetFull (A B : GSet) : GSet where
  V := A.V → B.V
  ρ :=
    { toFun := fun π => TypeCat.ofHom fun f x => B.act π (f (A.act π⁻¹ x))
      map_one' := by
        apply ConcreteCategory.hom_ext; intro f; funext x
        show B.act 1 (f (A.act (1 : PermAtom)⁻¹ x)) = f x
        rw [inv_one, GSet.act_one, GSet.act_one]
      map_mul' := fun a b => by
        apply ConcreteCategory.hom_ext; intro f; funext x
        show B.act (a * b) (f (A.act (a * b)⁻¹ x))
          = B.act a (B.act b (f (A.act b⁻¹ (A.act a⁻¹ x))))
        rw [GSet.act_mul, mul_inv_rev, GSet.act_mul] }

@[simp] lemma funGSetFull_ρ (A B : GSet) (π : PermAtom) (f : A.V → B.V) (x : A.V) :
    (funGSetFull A B).act π f x = B.act π (f (A.act π⁻¹ x)) := rfl

/-- Carrier of the internal hom: finitely supported functions for the conjugation action. -/
def funCarrier (A B : GSet) : Type := { f : A.V → B.V // HasFinSupport (funGSetFull A B) f }

/-- The internal-hom `G`-set: the conjugation action restricted to finitely supported functions.
The restriction is well defined because supports are equivariant (`Supports.smul`). -/
def funGSet (A B : GSet) : GSet where
  V := funCarrier A B
  ρ :=
    { toFun := fun π => TypeCat.ofHom fun f =>
        ⟨(funGSetFull A B).act π f.1, by
          obtain ⟨s, hs⟩ := f.2
          exact ⟨s.image π, hs.smul π⟩⟩
      map_one' := by
        apply ConcreteCategory.hom_ext; intro f
        apply Subtype.ext
        show (funGSetFull A B).act 1 f.1 = f.1
        rw [GSet.act_one]
      map_mul' := fun a b => by
        apply ConcreteCategory.hom_ext; intro f
        apply Subtype.ext
        show (funGSetFull A B).act (a * b) f.1
          = (funGSetFull A B).act a ((funGSetFull A B).act b f.1)
        rw [GSet.act_mul] }

@[simp] lemma funGSet_ρ_coe (A B : GSet) (π : PermAtom) (f : funCarrier A B) :
    ((funGSet A B).act π f).1 = (funGSetFull A B).act π f.1 := rfl

/-- The internal-hom `G`-set is nominal: each element carries its finite-support witness. -/
lemma funGSet_isNominal (A B : GSet) : IsNominal (funGSet A B) := by
  rintro ⟨f, s, hs⟩
  refine ⟨s, ?_⟩
  intro π hπ
  apply Subtype.ext
  show (funGSetFull A B).act π f = f
  exact hs π hπ

/-- The internal-hom object `funObj B C : Nom`. -/
def funObj (B C : Nom) : Nom :=
  Nom.of (funGSet B.obj C.obj) (funGSet_isNominal B.obj C.obj)

@[inherit_doc] infixr:70 " ⊸ₙ " => funObj

/-- **Supported-function transport.**  A finitely supported function commutes with every
permutation fixing one of its supports: if `s` supports `f` and `π` fixes `s` pointwise then
`f (B.ρ π b) = C.ρ π (f b)`.  This is the equivariance underlying the internal hom and is the
"movable" half of the determined-by-fresh-values property. -/
lemma funGSetFull_apply_of_supports {B C : GSet} {s : Finset Atom} {f : B.V → C.V}
    (hf : Supports (funGSetFull B C) s f) {π : PermAtom} (hπ : ∀ a ∈ s, π a = a) (b : B.V) :
    f (B.act π b) = C.act π (f b) := by
  have h2 := congrFun (hf π hπ) (B.act π b)
  simp only [funGSetFull_ρ] at h2
  rw [← GSet.act_mul, inv_mul_cancel, GSet.act_one] at h2
  exact h2.symm

/-! ### The internal-hom functor `B ⊸ₙ ·`

Postcomposition makes `B ⊸ₙ ·` a functor `Nom ⥤ Nom` (the object part of the intended right
adjoint `ihom B`). -/

/-- Underlying `Action.Hom` of postcomposition by a morphism `k : C ⟶ C'`. -/
def funMapActionHom {B C C' : Nom} (k : C ⟶ C') :
    funGSet B.obj C.obj ⟶ funGSet B.obj C'.obj where
  hom := TypeCat.ofHom fun f =>
    ⟨fun x => k.hom.hom (f.1 x), by
      obtain ⟨s, hs⟩ := f.2
      refine ⟨s, ?_⟩
      intro π hπ
      funext x
      show C'.obj.act π (k.hom.hom (f.1 (B.obj.act π⁻¹ x))) = k.hom.hom (f.1 x)
      have hk : k.hom.hom (C.obj.act π (f.1 (B.obj.act π⁻¹ x)))
          = C'.obj.act π (k.hom.hom (f.1 (B.obj.act π⁻¹ x))) := by
        have hcomm := ConcreteCategory.congr_hom (k.hom.comm π) (f.1 (B.obj.act π⁻¹ x))
        simpa only [ConcreteCategory.comp_apply] using hcomm
      rw [← hk]
      have hf' : C.obj.act π (f.1 (B.obj.act π⁻¹ x)) = f.1 x := by
        have := congrFun (hs π hπ) x
        simpa only [funGSetFull_ρ] using this
      rw [hf']⟩
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro f
    apply Subtype.ext
    funext x
    show k.hom.hom ((funGSetFull B.obj C.obj).act π f.1 x)
      = (funGSetFull B.obj C'.obj).act π (fun y => k.hom.hom (f.1 y)) x
    simp only [funGSetFull_ρ]
    have hcomm := ConcreteCategory.congr_hom (k.hom.comm π) (f.1 (B.obj.act π⁻¹ x))
    simpa only [ConcreteCategory.comp_apply] using hcomm

/-- The internal-hom functor `B ⊸ₙ · : Nom ⥤ Nom` (the object part of `ihom B`). -/
def funObjFunctor (B : Nom) : Nom ⥤ Nom where
  obj C := B ⊸ₙ C
  map k := ObjectProperty.homMk (funMapActionHom k)
  map_id := by
    intro C
    apply ObjectProperty.hom_ext
    ext f
    rfl
  map_comp := by
    intro C C' C'' k k'
    apply ObjectProperty.hom_ext
    ext f
    rfl

/-! ## STEP 2 — evaluation and uncurrying -/

/-- Underlying evaluation `Action.Hom`: apply a finitely supported function to a separated
argument.  It is equivariant because the conjugation action cancels the inner `π⁻¹` against the
argument's `π`. -/
def evalActionHom (B C : Nom) :
    sepGSet (funGSet B.obj C.obj) B.obj ⟶ C.obj where
  hom := TypeCat.ofHom fun p => p.1.1.1 p.1.2
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro p
    show ((funGSet B.obj C.obj).act π p.1.1).1 (B.obj.act π p.1.2)
      = C.obj.act π (p.1.1.1 p.1.2)
    simp only [funGSet_ρ_coe, funGSetFull_ρ]
    rw [← GSet.act_mul, inv_mul_cancel, GSet.act_one]

/-- The **evaluation** morphism `(B ⊸ₙ C) ⊗ₙ B ⟶ C` (the counit component of the intended
adjunction): evaluate a finitely supported function at a separated argument. -/
def evalHom (B C : Nom) : (B ⊸ₙ C) ⊗ₙ B ⟶ C :=
  ObjectProperty.homMk (evalActionHom B C)

/-- Underlying `Action.Hom` of the uncurried morphism. -/
def uncurryActionHom {A B C : Nom} (h : A ⟶ B ⊸ₙ C) :
    sepGSet A.obj B.obj ⟶ C.obj where
  hom := TypeCat.ofHom fun p => (h.hom.hom p.1.1).1 p.1.2
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro p
    have hc : h.hom.hom (A.obj.act π p.1.1)
        = (funGSet B.obj C.obj).act π (h.hom.hom p.1.1) := by
      have := ConcreteCategory.congr_hom (h.hom.comm π) p.1.1
      simpa only [ConcreteCategory.comp_apply] using this
    show (h.hom.hom (A.obj.act π p.1.1)).1 (B.obj.act π p.1.2)
      = C.obj.act π ((h.hom.hom p.1.1).1 p.1.2)
    rw [hc]
    simp only [funGSet_ρ_coe, funGSetFull_ρ]
    rw [← GSet.act_mul, inv_mul_cancel, GSet.act_one]

/-- **Uncurrying**: transpose a morphism `A ⟶ (B ⊸ₙ C)` to a morphism `A ⊗ₙ B ⟶ C`.  This is a
genuine equivariant morphism of nominal sets. -/
def uncurry {A B C : Nom} (h : A ⟶ B ⊸ₙ C) : A ⊗ₙ B ⟶ C :=
  ObjectProperty.homMk (uncurryActionHom h)

/-- β-rule for uncurrying: on a separated pair it is application. -/
@[simp] lemma uncurry_apply {A B C : Nom} (h : A ⟶ B ⊸ₙ C)
    (p : sepCarrier A.obj B.obj) :
    (uncurry h).hom.hom p = (h.hom.hom p.1.1).1 p.1.2 := rfl

/-- Uncurrying is exactly `evalHom` precomposed with `h` whiskered on the left: this witnesses
`evalHom` as the counit through which every transpose factors. -/
lemma uncurry_eq_whisker_eval {A B C : Nom} (h : A ⟶ B ⊸ₙ C) :
    uncurry h = MonoidalCategory.whiskerRight h B ≫ evalHom B C := by
  apply ObjectProperty.hom_ext
  ext p
  rfl

/-! ### The transpose is determined on the separated locus

The value of any curried transpose `h` of `g` is pinned on separated pairs; two transposes of the
same `g` therefore agree on the separated (fresh) locus.  Extending this agreement to *all*
arguments — hence uncurrying's injectivity and the totalization of `curry` — is the determined-by-
fresh-values residual documented below. -/

/-- Any transpose `h` of `g` (i.e. `uncurry h = g`) recovers `g` on separated pairs. -/
lemma transpose_apply_on_sep {A B C : Nom} (g : A ⊗ₙ B ⟶ C) (h : A ⟶ B ⊸ₙ C)
    (hg : uncurry h = g) (a : A.obj.V) (b : B.obj.V) (hsep : Separated A.obj B.obj a b) :
    (h.hom.hom a).1 b = g.hom.hom ⟨(a, b), hsep⟩ := by
  subst hg; rfl

/-- Two transposes of the same morphism agree on the separated locus. -/
lemma transpose_agree_on_sep {A B C : Nom} (h h' : A ⟶ B ⊸ₙ C)
    (heq : uncurry h = uncurry h') (a : A.obj.V) (b : B.obj.V)
    (hsep : Separated A.obj B.obj a b) :
    (h.hom.hom a).1 b = (h'.hom.hom a).1 b := by
  have := congrArg (fun (m : A ⊗ₙ B ⟶ C) => m.hom.hom ⟨(a, b), hsep⟩) heq
  simpa using this

/-! ## STEP 3 — the adjunction and `MonoidalClosed Nom`

The data of the right adjoint `ihom B = funObjFunctor B` to the separated tensor is provided above
and is non-vacuous:

* the internal-hom **object** `B ⊸ₙ C` (`funObj`, `funGSet_isNominal`) — STEP 1;
* the internal-hom **functor** `funObjFunctor B : Nom ⥤ Nom` (postcomposition, with `map_id`,
  `map_comp`);
* the **evaluation / counit component** `evalHom : (B ⊸ₙ C) ⊗ₙ B ⟶ C`;
* the **uncurry** transpose `A ⟶ (B ⊸ₙ C)  ↦  A ⊗ₙ B ⟶ C`, with `uncurry h = h ▷ B ≫ evalHom`.

`Closed B` (adjoint `- ⊗ₙ B ⊣ funObjFunctor B`) and hence `MonoidalClosed Nom` are completed and
registered as `Nominal.monoidalClosedNom` in `CatCrypt.Category.NominalMonoidalClosedComplete`,
using the separated exponential `⊸ₛ` (the fresh-agreement quotient of the raw function space) as the
internal hom rather than `funObj` directly. That construction supplies the inverse transpose
`curry : (A ⊗ₙ B ⟶ C) → (A ⟶ B ⊸ₛ C)` and the two round trips; the discussion below records the
key nominal ingredient, the totalization of `curry`.
`transpose_apply_on_sep`/`transpose_agree_on_sep` show the transpose is pinned on separated pairs;
the totalizing step is:

### Totalizing `curry` — the determined-by-fresh-values property

Given `g : A ⊗ₙ B ⟶ C` and `a : A.obj.V`, the curried function `curry g a : B.obj.V → C.obj.V`
must be **total**, yet `g` supplies values only on separated pairs.  On a separated argument `b`
(`supp b ∩ supp a = ∅`) the value is `g ⟨(a, b), _⟩`.  On a **non-separated** `b` the value is
*forced*, not free: `curry g a` must be finitely supported by `supp a`, and a finite-support
function is uniquely determined by its values on arguments *fresh* for its support (Pitts, *Nominal
Sets*).  A single fresh renaming cannot compute this value, because an atom of `supp a ∩ supp b`
cannot be moved out of `supp a` by any permutation fixing `supp a`.  The provided
`funGSetFull_apply_of_supports` is exactly the *movable* half of this determination (transport by a
support-fixing permutation); the fixed-overlap half is the classical freshness/`some/any`-quantifier
theorem, and is the load-bearing residual.

Concretely, the ingredients are:

* `curry g a` is a well-defined *total* finitely-supported function extending `b ↦ g ⟨(a,b),_⟩`
  from the fresh locus (existence of the unique FS extension);
* `a ↦ curry g a` is equivariant (a `Nom` morphism `A ⟶ B ⊸ₛ C`);
* `uncurry (curry g) = g` (immediate on separated pairs via `uncurry_apply`) and
  `curry (uncurry h) = h` (via `funGSetFull_apply_of_supports` on the fresh locus and
  determined-by-fresh elsewhere), plus adjunction naturality.

These assemble `tensorRight B ⊣ (B ⊸ₛ ·)`, hence `Closed B` and `MonoidalClosed Nom`, carried out
over the separated exponential `⊸ₛ` in `NominalMonoidalClosedComplete`. -/

end Nominal
