/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.Nominal
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

/-!
# Atom abstraction `[𝔸](−)` as an endofunctor on `Nom`

This file builds the **name-abstraction** construction of Pitts' nominal sets directly on the
categorical category `Nom` from `CatCrypt.Category.Nominal` (the full subcategory of
finite-support `PermAtom`-sets), **without** routing through any equivalence with a `NomSet`
typeclass. It mirrors the template
`CatCryptCore/Nominal/NameAbstraction.lean`, but works over the *full* permutation group
`PermAtom = Equiv.Perm Atom` and for an arbitrary `GSet`/`Nom` object `X` (acting via `X.ρ`),
rather than a `NomSet` instance with a canonical least support.

The key design choice that keeps every proof elementary is the **cofinite** formulation of
α-equivalence: `(a, x) ~ (b, y)` holds iff the swapped representatives
`swap a c • x` and `swap b c • y` agree for *all but finitely many* atoms `c` (i.e. for all `c`
outside some finite set). This avoids constructing a canonical support (which `Nom` objects do
not carry — they only have `HasFinSupport`, an existential), and makes reflexivity/symmetry/
transitivity of the relation immediate.

## Main definitions

* `atomObj` (`𝔸`) — the nominal set of atoms.
* `AbsRel X` / `absSetoid X` — the α-equivalence relation and its setoid.
* `absGSet X`, `absObj X` — the abstraction `[𝔸]X` as a `GSet` / `Nom` object, with the
  diagonal action and its finite-support proof (support shrinks: `supp x \ {a}` supports the
  class of `(a, x)`).
* `absF : Nom ⥤ Nom` — atom abstraction as an endofunctor.
* `absPt`, `absPt_equivariant`, `absPt_rename` — the abstraction point map and its renaming law.

## Main results

* `absGSet_isNominal` — `[𝔸]X` is a nominal set (finite support of a class via support-shrink).
* `absF` is a genuine `CategoryTheory.Functor` (`map_id`, `map_comp` proved).

## Residual: concretion

The elimination map `concretize a ⟦(b, x)⟧ = swap a b • x` (opening an abstraction at a fresh
atom) is **not** provided here. Pitts' concretion is well defined only for `a` fresh for the
class, and its well-definedness proof rests on the *some/any* freshness principle together with a
canonical least support of the representative. `Nom` objects carry only `HasFinSupport` (an
existential support), not a canonical `supp`; the missing prerequisite is the least-support theory
(closure of finite supports under intersection, giving `supp x := ⋂ {s | Supports X s x}`), which
is the standard nontrivial nominal-sets result and is the single identified prerequisite for the
concretion map and its computation rule. The abstraction side (`absPt` with `absPt_equivariant`
and `absPt_rename`) needs no canonical support and is delivered in full.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

namespace Nominal

/-! ## Permutation-action helpers -/

/-- If two permutations `g` and `h` agree on a support `s` of `x`, they act equally on `x`. -/
lemma act_eq_of_agree {X : GSet} {s : Finset Atom} {x : X.V}
    (hs : Supports X s x) {g h : PermAtom} (hgh : ∀ a ∈ s, g a = h a) :
    X.act g x = X.act h x := by
  have key : ∀ a ∈ s, (h⁻¹ * g) a = a := by
    intro a ha
    simp [Equiv.Perm.mul_apply, hgh a ha]
  calc X.act g x = X.act (h * (h⁻¹ * g)) x := by rw [mul_inv_cancel_left]
    _ = X.act h (X.act (h⁻¹ * g) x) := GSet.act_mul X h (h⁻¹ * g) x
    _ = X.act h x := by rw [hs _ key]

/-- Conjugation of a transposition through a permutation:
`swap (π a) (π b) * π = π * swap a b`. -/
lemma swap_mul_perm (π : PermAtom) (a b : Atom) :
    Equiv.swap (π a) (π b) * π = π * Equiv.swap a b := by
  ext d
  simp only [Equiv.Perm.mul_apply]
  by_cases hda : d = a
  · subst hda; simp only [Equiv.swap_apply_left]
  · by_cases hdb : d = b
    · subst hdb; simp only [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hda hdb,
          Equiv.swap_apply_of_ne_of_ne (fun h => hda (π.injective h))
            (fun h => hdb (π.injective h))]

/-! ## The object of atoms `𝔸` -/

/-- The nominal set of atoms `𝔸` (an alias for `Nominal.atomObj` from `Nominal.lean`, restated
here so this file is self-contained at the abstraction level). -/
abbrev atomObj' : Nom := atomObj

/-! ## The α-equivalence relation -/

/-- α-equivalence on representatives `Atom × X.V`, cofinite form: the swapped representatives
agree at every atom outside some finite set. -/
def AbsRel (X : GSet) (p q : Atom × X.V) : Prop :=
  ∃ s : Finset Atom, ∀ c ∉ s, X.act (Equiv.swap p.1 c) p.2 = X.act (Equiv.swap q.1 c) q.2

namespace AbsRel

variable {X : GSet}

/-- Reflexivity. -/
theorem refl (p : Atom × X.V) : AbsRel X p p := ⟨∅, fun _ _ => rfl⟩

/-- Symmetry. -/
theorem symm {p q : Atom × X.V} (h : AbsRel X p q) : AbsRel X q p := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun c hc => (hs c hc).symm⟩

/-- Transitivity. -/
theorem trans {p q r : Atom × X.V} (hpq : AbsRel X p q) (hqr : AbsRel X q r) :
    AbsRel X p r := by
  obtain ⟨s₁, h₁⟩ := hpq
  obtain ⟨s₂, h₂⟩ := hqr
  refine ⟨s₁ ∪ s₂, fun c hc => ?_⟩
  rw [Finset.mem_union, not_or] at hc
  exact (h₁ c hc.1).trans (h₂ c hc.2)

end AbsRel

/-- The setoid for atom abstraction. -/
def absSetoid (X : GSet) : Setoid (Atom × X.V) where
  r := AbsRel X
  iseqv := ⟨AbsRel.refl, AbsRel.symm, AbsRel.trans⟩

/-- α-equivalence is preserved by the diagonal permutation action. -/
theorem AbsRel_smul {X : GSet} (π : PermAtom) {p q : Atom × X.V} (h : AbsRel X p q) :
    AbsRel X (π p.1, X.act π p.2) (π q.1, X.act π q.2) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s.image π, fun d hd => ?_⟩
  -- `d` outside `π '' s` means `π⁻¹ d ∉ s`
  have hdc : π (π⁻¹ d) = d := by simp
  have hc : π⁻¹ d ∉ s := fun hmem =>
    hd (by simpa [hdc] using Finset.mem_image_of_mem π hmem)
  have hkey := hs (π⁻¹ d) hc
  calc X.act (Equiv.swap (π p.1) d) (X.act π p.2)
      = X.act (Equiv.swap (π p.1) (π (π⁻¹ d)) * π) p.2 := by
        rw [hdc, ← GSet.act_mul]
    _ = X.act (π * Equiv.swap p.1 (π⁻¹ d)) p.2 := by rw [swap_mul_perm]
    _ = X.act π (X.act (Equiv.swap p.1 (π⁻¹ d)) p.2) := GSet.act_mul X _ _ _
    _ = X.act π (X.act (Equiv.swap q.1 (π⁻¹ d)) q.2) := by rw [hkey]
    _ = X.act (π * Equiv.swap q.1 (π⁻¹ d)) q.2 := (GSet.act_mul X _ _ _).symm
    _ = X.act (Equiv.swap (π q.1) (π (π⁻¹ d)) * π) q.2 := by rw [swap_mul_perm]
    _ = X.act (Equiv.swap (π q.1) d) (X.act π q.2) := by rw [hdc, ← GSet.act_mul]

/-! ## The abstraction `GSet` -/

/-- The underlying `GSet` of `[𝔸]X`: the quotient of `Atom × X.V` by α-equivalence, with the
diagonal action `π • ⟦(a, x)⟧ = ⟦(π a, X.act π x)⟧`. -/
def absGSet (X : GSet) : GSet where
  V := Quotient (absSetoid X)
  ρ :=
    { toFun := fun π => TypeCat.ofHom
        (Quotient.map (fun p => (π p.1, X.act π p.2)) (fun _ _ h => AbsRel_smul π h))
      map_one' := by
        apply ConcreteCategory.hom_ext; intro q
        induction q using Quotient.inductionOn with
        | _ p =>
          show Quotient.mk (absSetoid X) ((1 : PermAtom) p.1, X.act (1 : PermAtom) p.2)
            = Quotient.mk (absSetoid X) p
          rw [Equiv.Perm.one_apply, GSet.act_one]
      map_mul' := fun a b => by
        apply ConcreteCategory.hom_ext; intro q
        induction q using Quotient.inductionOn with
        | _ p =>
          show Quotient.mk (absSetoid X) ((a * b) p.1, X.act (a * b) p.2)
            = Quotient.mk (absSetoid X) (a (b p.1), X.act a (X.act b p.2))
          rw [GSet.act_mul]; rfl }

/-- Abstraction point: the class of `(a, x)` in `[𝔸]X`. -/
def absPt (X : GSet) (a : Atom) (x : X.V) : (absGSet X).V :=
  Quotient.mk (absSetoid X) (a, x)

@[simp] lemma absGSet_ρ_mk (X : GSet) (π : PermAtom) (a : Atom) (x : X.V) :
    (absGSet X).act π (absPt X a x) = absPt X (π a) (X.act π x) := rfl

/-- **Support-shrink**: if `s` supports `x`, then `s \ {a}` supports the class of `(a, x)`.
This is the crux finite-support lemma for atom abstraction. -/
theorem absGSet_supports {X : GSet} {s : Finset Atom} {a : Atom} {x : X.V}
    (hs : Supports X s x) : Supports (absGSet X) (s \ {a}) (absPt X a x) := by
  intro π hπ
  show Quotient.mk (absSetoid X) (π a, X.act π x) = Quotient.mk (absSetoid X) (a, x)
  apply Quotient.sound
  -- Goal: AbsRel X (π a, X.act π x) (a, x).  Witness: s ∪ {a, π a}.
  refine ⟨insert a (insert (π a) s), fun c hc => ?_⟩
  simp only [Finset.mem_insert, not_or] at hc
  obtain ⟨hca, hcπa, hcs⟩ := hc
  -- reduce to a permutation-agreement statement on `s`
  show X.act (Equiv.swap (π a) c) (X.act π x) = X.act (Equiv.swap a c) x
  rw [← GSet.act_mul]
  apply act_eq_of_agree hs
  intro d hd
  -- (swap (π a) c * π) d = swap a c d  for d ∈ s
  rw [Equiv.Perm.mul_apply]
  by_cases hda : d = a
  · subst hda
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · -- d ∈ s, d ≠ a  ⟹  π d = d, d ≠ π a, d ≠ c
    have hπd : π d = d := hπ d (Finset.mem_sdiff.mpr ⟨hd, Finset.notMem_singleton.mpr hda⟩)
    have hdc : d ≠ c := fun h => hcs (h ▸ hd)
    have hdπa : d ≠ π a := by
      intro h
      -- π d = d and π a = d ⟹ a = d by injectivity, contra d ≠ a
      exact hda (π.injective (by rw [hπd, h]))
    rw [hπd, Equiv.swap_apply_of_ne_of_ne hdπa hdc, Equiv.swap_apply_of_ne_of_ne hda hdc]

/-- `[𝔸]X` is a nominal set: every class has finite support (`supp x \ {a}`). -/
theorem absGSet_isNominal {X : GSet} (hX : IsNominal X) : IsNominal (absGSet X) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    obtain ⟨s, hs⟩ := hX p.2
    exact ⟨s \ {p.1}, absGSet_supports hs⟩

/-- Atom abstraction `[𝔸]X` on objects of `Nom`. -/
def absObj (X : Nom) : Nom := Nom.of (absGSet X.obj) (absGSet_isNominal X.property)

@[inherit_doc] notation "[𝔸]" X => absObj X

/-! ## Functoriality -/

/-- α-equivalence is transported along an equivariant map (used for the map on morphisms). -/
theorem AbsRel_map {X Y : GSet} (f : X ⟶ Y) {p q : Atom × X.V} (h : AbsRel X p q) :
    AbsRel Y (p.1, f.hom p.2) (q.1, f.hom q.2) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun c hc => ?_⟩
  have e := hs c hc
  -- push `f.hom` through the swap actions via equivariance `f.comm`
  have fp : f.hom (X.act (Equiv.swap p.1 c) p.2) = Y.act (Equiv.swap p.1 c) (f.hom p.2) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (f.comm (Equiv.swap p.1 c)) p.2
  have fq : f.hom (X.act (Equiv.swap q.1 c) q.2) = Y.act (Equiv.swap q.1 c) (f.hom q.2) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (f.comm (Equiv.swap q.1 c)) q.2
  rw [← fp, ← fq, e]

/-- The action of atom abstraction on a morphism `f : X ⟶ Y` of `GSet`s. -/
def absHom {X Y : GSet} (f : X ⟶ Y) : absGSet X ⟶ absGSet Y where
  hom := TypeCat.ofHom (Quotient.map (fun p => (p.1, f.hom p.2)) (fun _ _ h => AbsRel_map f h))
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      show Quotient.mk (absSetoid Y) (π p.1, f.hom (X.act π p.2))
        = Quotient.mk (absSetoid Y) (π p.1, Y.act π (f.hom p.2))
      have hc : f.hom (X.act π p.2) = Y.act π (f.hom p.2) := by
        simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (f.comm π) p.2
      rw [hc]

@[simp] lemma absHom_mk {X Y : GSet} (f : X ⟶ Y) (a : Atom) (x : X.V) :
    (absHom f).hom (absPt X a x) = absPt Y a (f.hom x) := rfl

/-- Atom abstraction as an endofunctor on `Nom`. -/
def absF : Nom ⥤ Nom where
  obj X := absObj X
  map {X Y} f := ⟨absHom f.hom⟩
  map_id X := by
    apply InducedCategory.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext; intro q
    induction q using Quotient.inductionOn with
    | _ p => rfl
  map_comp {X Y Z} f g := by
    apply InducedCategory.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext; intro q
    induction q using Quotient.inductionOn with
    | _ p => rfl

/-! ## Abstraction point: equivariance and renaming -/

/-- Equivariance of the abstraction point: `π • ⟦(a, x)⟧ = ⟦(π a, π • x)⟧`. -/
theorem absPt_equivariant (X : GSet) (π : PermAtom) (a : Atom) (x : X.V) :
    (absGSet X).act π (absPt X a x) = absPt X (π a) (X.act π x) := rfl

/-- **Renaming law** for the abstraction point: if `b` is fresh for `x` (outside a support `s`
of `x`) and `b ≠ a`, then abstracting at `a` equals abstracting at `b` after swapping. -/
theorem absPt_rename {X : GSet} {s : Finset Atom} {a b : Atom} {x : X.V}
    (hs : Supports X s x) (hb : b ∉ s) (hba : b ≠ a) :
    absPt X a x = absPt X b (X.act (Equiv.swap a b) x) := by
  apply Quotient.sound
  -- Goal: AbsRel X (a, x) (b, swap a b • x).  Witness s ∪ {a, b}.
  refine ⟨insert a (insert b s), fun c hc => ?_⟩
  simp only [Finset.mem_insert, not_or] at hc
  obtain ⟨hca, hcb, hcs⟩ := hc
  show X.act (Equiv.swap a c) x = X.act (Equiv.swap b c) (X.act (Equiv.swap a b) x)
  rw [← GSet.act_mul]
  apply act_eq_of_agree hs
  intro d hd
  have hdc : d ≠ c := fun h => hcs (h ▸ hd)
  have hdb : d ≠ b := fun h => hb (h ▸ hd)
  rw [Equiv.Perm.mul_apply]
  by_cases hda : d = a
  · subst hda
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne hda hdc, Equiv.swap_apply_of_ne_of_ne hda hdb,
        Equiv.swap_apply_of_ne_of_ne hdb hdc]

end Nominal
