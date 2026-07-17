/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Group

set_option autoImplicit false

/-!
# Nominal sets as a G-set subcategory, toward the separated-product monoidal structure

This file develops the categorical structure of **nominal sets** (the Schanuel topos `Nom`)
on top of Mathlib's `CategoryTheory.Action` machinery, working toward the statement that
`Nom` is symmetric monoidal closed under the *separated* (a.k.a. *disjoint-support*) product.

We reuse Mathlib maximally: `Nom` is realized as a full subcategory of
`Action (Type) (Equiv.Perm Atom)` — the category of `G`-sets for the permutation group of a
countable set of atoms — cut out by the finite-support predicate. All of the category
structure (composition, isos, the forgetful functor) is inherited from `Action`.

## Design note on `Action.Continuous`

Mathlib's `Action.Continuous` cuts out the *continuous* actions, but only relative to a
`HasForget₂ V TopCat` factorization of the ambient category and a topology on the acting monoid
`G`. Recovering "finite support" as "continuity for the pro-finite/permutation topology" would
require equipping `Type` and `Equiv.Perm Atom` with those topologies and proving the
identification. That is a substantial detour, so we instead take the direct, standard route: a
bespoke `Supports` / `IsNominal` finite-support predicate. See `IsNominal`.

## Milestones

* **M1** — the category `Nom` (this section is complete): the finite-support predicate,
  its equivariance, `Nom` as a `FullSubcategory`, its inherited `Category` instance, and the
  basic objects (the one-point unit `𝟙ₙ` and the object of atoms `𝔸`).
* **M2** — the separated product `⊗ₙ` as (symmetric) monoidal structure: the object map with
  its finite-support proof, the diagonal action, functoriality on morphisms, the unit, and the
  braiding / unitor components. See the section header for the precise list of what is and is
  not closed.
* **M3** — monoidal closure (`⊸`): documented as a residual; see the closing section.

## Main definitions

* `GSet` — `Action (Type) (Equiv.Perm Atom)`, the ambient `G`-sets.
* `Supports`, `IsNominal` — the finite-support predicate on objects/elements.
* `Nom` — the full subcategory of finite-support `G`-sets.
* `sepObj A B` (`A ⊗ₙ B`) — the separated product object.
* `unitObj` (`𝟙ₙ`) — the monoidal unit.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

namespace Nominal

/-- Atoms: a countably infinite set of names. -/
abbrev Atom : Type := ℕ

/-- The acting group: all finitary-or-not permutations of atoms. -/
abbrev PermAtom : Type := Equiv.Perm Atom

/-- The ambient category of `G`-sets for `G = Equiv.Perm Atom`, reusing Mathlib's `Action`.
An object `X` bundles a carrier `X.V : Type` with a monoid hom `X.ρ : PermAtom →* End X.V`;
`X.ρ π x` is the (left) action of the permutation `π` on `x`. -/
abbrev GSet : Type _ := Action (Type) PermAtom

namespace GSet

variable (X : GSet)

/-- Apply a `G`-set action to a point. In Lean 4.30 the `End`-valued action
`X.ρ π : End X.V` is a categorical endomorphism rather than a bare function, so
applying it to a point goes through `ConcreteCategory.hom`. -/
abbrev act (π : PermAtom) (x : X.V) : X.V := ConcreteCategory.hom (X.ρ π) x

/-- The action is a left action: the identity permutation acts as the identity. -/
@[simp] lemma act_one (x : X.V) : X.act 1 x = x := by
  simp [act, Action.ρ_one]

/-- The action is a left action: it turns products of permutations into composition. -/
lemma act_mul (a b : PermAtom) (x : X.V) : X.act (a * b) x = X.act a (X.act b x) := by
  simp [act, map_mul]

end GSet

/-! ## M1 — the category `Nom` -/

/-- `s` **supports** `x` when every permutation fixing `s` pointwise fixes `x`. -/
def Supports (X : GSet) (s : Finset Atom) (x : X.V) : Prop :=
  ∀ π : PermAtom, (∀ a ∈ s, π a = a) → X.act π x = x

/-- Equivariance of support: if `s` supports `x` then `π • s` supports `π • x`. This is the
key lemma making the diagonal action on the separated product well defined. -/
lemma Supports.smul {X : GSet} {s : Finset Atom} {x : X.V}
    (h : Supports X s x) (π : PermAtom) :
    Supports X (s.image π) (X.act π x) := by
  intro σ hσ
  have key : ∀ a ∈ s, (π⁻¹ * σ * π) a = a := by
    intro a ha
    have hmem : π a ∈ s.image π := Finset.mem_image_of_mem π ha
    have hfix : σ (π a) = π a := hσ (π a) hmem
    simp [Equiv.Perm.mul_apply, hfix]
  have e : σ * π = π * (π⁻¹ * σ * π) := by group
  calc X.act σ (X.act π x) = X.act (σ * π) x := (GSet.act_mul X σ π x).symm
    _ = X.act (π * (π⁻¹ * σ * π)) x := by rw [e]
    _ = X.act π (X.act (π⁻¹ * σ * π) x) := GSet.act_mul X _ _ x
    _ = X.act π x := by rw [h _ key]

/-- An element has finite support if some finite set supports it. -/
def HasFinSupport (X : GSet) (x : X.V) : Prop := ∃ s : Finset Atom, Supports X s x

/-- A `G`-set is **nominal** when every element has finite support. -/
def IsNominal (X : GSet) : Prop := ∀ x : X.V, HasFinSupport X x

/-- `Nom`, the category of nominal sets: the full subcategory of finite-support `G`-sets.
The `Category` instance is inherited from `Action` via `ObjectProperty.FullSubcategory`. -/
abbrev Nom : Type _ := ObjectProperty.FullSubcategory IsNominal

/-- Package a `G`-set together with a proof it is nominal as an object of `Nom`. -/
abbrev Nom.of (X : GSet) (h : IsNominal X) : Nom := ⟨X, h⟩

example : Category Nom := inferInstance

/-! ### Basic objects -/

/-- The one-point nominal set, carrier `PUnit` with the trivial action; it is the monoidal unit
`𝟙ₙ`. Its single element is supported by `∅`. -/
def unitGSet : GSet := Action.trivial PermAtom PUnit

lemma unitGSet_isNominal : IsNominal unitGSet := fun _ => ⟨∅, fun _ _ => rfl⟩

/-- The monoidal unit `𝟙ₙ` of `Nom`. -/
def unitObj : Nom := Nom.of unitGSet unitGSet_isNominal

@[inherit_doc] notation "𝟙ₙ" => unitObj

/-- The object of atoms `𝔸`: carrier `Atom`, acted on by evaluation of the permutation.
Every atom `a` is supported by `{a}`. -/
def atomGSet : GSet where
  V := Atom
  ρ :=
    { toFun := fun π => TypeCat.ofHom (π : Atom → Atom)
      map_one' := rfl
      map_mul' := fun a b => by
        apply ConcreteCategory.hom_ext; intro x; rfl }

lemma atomGSet_isNominal : IsNominal atomGSet :=
  fun a => ⟨{a}, fun _ hπ => hπ a (Finset.mem_singleton_self a)⟩

/-- The nominal set of atoms `𝔸`. -/
def atomObj : Nom := Nom.of atomGSet atomGSet_isNominal

/-- Supports are transported forward along equivariant maps: if `s` supports `a` in `A` and
`f : A ⟶ A'` is a `G`-map, then `s` supports `f a` in `A'`. -/
lemma Supports.map {A A' : GSet} (f : A ⟶ A') {s : Finset Atom} {a : A.V}
    (h : Supports A s a) : Supports A' s (f.hom a) := by
  intro π hπ
  have hc : f.hom (A.act π a) = A'.act π (f.hom a) := by
    have hcomm := ConcreteCategory.congr_hom (f.comm π) a
    simpa only [ConcreteCategory.comp_apply] using hcomm
  rw [← hc, h π hπ]

/-! ## M2 — the separated (disjoint-support) product `⊗ₙ`

We define `A ⊗ₙ B` as the sub-`G`-set of pairs with *disjoint supports*, with the diagonal
action. We establish:

* the object map with its finite-support proof (`sepObj`, lands in `Nom`);
* functoriality on morphisms (`sepHom`) — giving the tensor bifunctor data;
* the symmetry `sepBraiding` and the two unitors `sepLeftUnitor`, `sepRightUnitor` as genuine
  isomorphisms of nominal sets.

What is **not** assembled here (documented residual): the full `MonoidalCategory Nom` typeclass
— specifically the associator and the coherence conditions (pentagon, triangle, hexagon). See
the closing section for the precise statement of the associator obstruction. We deliberately do
**not** register a `MonoidalCategory` instance, to avoid a vacuous one. -/

/-- Two elements are **separated** when they have disjoint finite supports. Equivalent, in the
presence of least supports, to `supp a ∩ supp b = ∅`; the existential form is manifestly
equivariant and avoids constructing the minimal support. -/
def Separated (A B : GSet) (a : A.V) (b : B.V) : Prop :=
  ∃ s t : Finset Atom, Supports A s a ∧ Supports B t b ∧ Disjoint s t

/-- Separation is symmetric. -/
lemma Separated.symm {A B : GSet} {a : A.V} {b : B.V} (h : Separated A B a b) :
    Separated B A b a := by
  obtain ⟨s, t, hs, ht, hd⟩ := h
  exact ⟨t, s, ht, hs, hd.symm⟩

/-- Separation is preserved by the diagonal action. -/
lemma Separated.smul {A B : GSet} {a : A.V} {b : B.V}
    (h : Separated A B a b) (π : PermAtom) :
    Separated A B (A.act π a) (B.act π b) := by
  obtain ⟨s, t, hs, ht, hd⟩ := h
  refine ⟨s.image π, t.image π, hs.smul π, ht.smul π, ?_⟩
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, hwu⟩ := hx'
  have : w = u := π.injective hwu
  subst this
  exact Finset.disjoint_left.mp hd hu hw

/-- Carrier of the separated product: pairs with disjoint supports. -/
def sepCarrier (A B : GSet) : Type := { p : A.V × B.V // Separated A B p.1 p.2 }

/-- The separated product of two `G`-sets, with the diagonal action. -/
def sepGSet (A B : GSet) : GSet where
  V := sepCarrier A B
  ρ :=
    { toFun := fun π => TypeCat.ofHom fun p => ⟨(A.act π p.1.1, B.act π p.1.2), p.2.smul π⟩
      map_one' := by
        apply ConcreteCategory.hom_ext; intro p
        apply Subtype.ext
        show (A.act 1 p.1.1, B.act 1 p.1.2) = (p.1.1, p.1.2)
        rw [GSet.act_one, GSet.act_one]
      map_mul' := fun a b => by
        apply ConcreteCategory.hom_ext; intro p
        apply Subtype.ext
        show (A.act (a * b) p.1.1, B.act (a * b) p.1.2)
          = (A.act a (A.act b p.1.1), B.act a (B.act b p.1.2))
        rw [GSet.act_mul, GSet.act_mul] }

/-- The separated product of nominal sets is nominal: if `s` supports `a` and `t` supports `b`,
then `s ∪ t` supports the pair. -/
lemma sepGSet_isNominal {A B : GSet} (hA : IsNominal A) (hB : IsNominal B) :
    IsNominal (sepGSet A B) := by
  rintro ⟨⟨a, b⟩, hsep⟩
  obtain ⟨s, hs⟩ := hA a
  obtain ⟨t, ht⟩ := hB b
  refine ⟨s ∪ t, ?_⟩
  intro π hπ
  refine Subtype.ext ?_
  have ha : A.act π a = a := hs π (fun x hx => hπ x (Finset.mem_union_left t hx))
  have hb : B.act π b = b := ht π (fun x hx => hπ x (Finset.mem_union_right s hx))
  show (A.act π a, B.act π b) = (a, b)
  rw [ha, hb]

/-- If `s` supports `a` and `t` supports `b`, then `s ∪ t` supports the pair `(a, b)` in the
separated product. -/
lemma sepGSet_supports_pair {A B : GSet} {s t : Finset Atom} {a : A.V} {b : B.V}
    (hsep : Separated A B a b) (hs : Supports A s a) (ht : Supports B t b) :
    Supports (sepGSet A B) (s ∪ t) ⟨(a, b), hsep⟩ := by
  intro π hπ
  apply Subtype.ext
  show (A.act π a, B.act π b) = (a, b)
  rw [hs π (fun x hx => hπ x (Finset.mem_union_left t hx)),
      ht π (fun x hx => hπ x (Finset.mem_union_right s hx))]

/-- Conversely, any support of a pair supports its first component. -/
lemma sepGSet_supports_fst {A B : GSet} {u : Finset Atom} {p : sepCarrier A B}
    (h : Supports (sepGSet A B) u p) : Supports A u p.1.1 :=
  fun π hπ => congrArg (fun z : sepCarrier A B => z.1.1) (h π hπ)

/-- Any support of a pair supports its second component. -/
lemma sepGSet_supports_snd {A B : GSet} {u : Finset Atom} {p : sepCarrier A B}
    (h : Supports (sepGSet A B) u p) : Supports B u p.1.2 :=
  fun π hπ => congrArg (fun z : sepCarrier A B => z.1.2) (h π hπ)

/-- The separated product `A ⊗ₙ B` of nominal sets. -/
def sepObj (A B : Nom) : Nom :=
  Nom.of (sepGSet A.obj B.obj) (sepGSet_isNominal A.property B.property)

@[inherit_doc] infixr:70 " ⊗ₙ " => sepObj

/-! ### Functoriality: the tensor bifunctor on morphisms -/

/-- The separated product acts on morphisms: `f ⊗ g` on disjoint-support pairs. Separation is
preserved because supports are (`Supports.map`). This is the action of the tensor bifunctor on
morphisms. -/
def sepHom {A A' B B' : GSet} (f : A ⟶ A') (g : B ⟶ B') :
    sepGSet A B ⟶ sepGSet A' B' where
  hom := TypeCat.ofHom fun p =>
    ⟨(f.hom p.1.1, g.hom p.1.2), by
      obtain ⟨s, t, hs, ht, hd⟩ := p.2
      exact ⟨s, t, hs.map f, ht.map g, hd⟩⟩
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro p
    apply Subtype.ext
    show (f.hom (A.act π p.1.1), g.hom (B.act π p.1.2))
      = (A'.act π (f.hom p.1.1), B'.act π (g.hom p.1.2))
    have fc : f.hom (A.act π p.1.1) = A'.act π (f.hom p.1.1) := by
      simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (f.comm π) p.1.1
    have gc : g.hom (B.act π p.1.2) = B'.act π (g.hom p.1.2) := by
      simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (g.comm π) p.1.2
    rw [fc, gc]

@[simp] lemma sepHom_id {A B : GSet} : sepHom (𝟙 A) (𝟙 B) = 𝟙 (sepGSet A B) := by
  ext p; rfl

@[simp] lemma sepHom_comp {A A' A'' B B' B'' : GSet}
    (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B'') :
    sepHom (f ≫ f') (g ≫ g') = sepHom f g ≫ sepHom f' g' := by
  ext p; rfl

/-! ### Symmetry (braiding) -/

/-- Underlying swap bijection of the braiding. -/
def sepBraidingEquiv (A B : GSet) : sepCarrier A B ≃ sepCarrier B A where
  toFun p := ⟨(p.1.2, p.1.1), p.2.symm⟩
  invFun p := ⟨(p.1.2, p.1.1), p.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The braiding `A ⊗ₙ B ≅ B ⊗ₙ A`: swapping a disjoint-support pair. -/
def sepBraiding (A B : Nom) : A ⊗ₙ B ≅ B ⊗ₙ A :=
  ObjectProperty.isoMk _
    (Action.mkIso (Equiv.toIso (sepBraidingEquiv A.obj B.obj)) (by intro π; ext p; rfl))

/-! ### Unitors -/

/-- `∅` supports the unique point of the unit nominal set. -/
lemma unitGSet_supports (u : unitGSet.V) : Supports unitGSet ∅ u :=
  fun _ _ => rfl

/-- Underlying bijection of the left unitor `𝟙ₙ ⊗ₙ A ≅ A`. -/
def sepLeftUnitorEquiv (A : Nom) : sepCarrier unitGSet A.obj ≃ A.obj.V where
  toFun p := p.1.2
  invFun a :=
    ⟨(PUnit.unit, a), by
      obtain ⟨t, ht⟩ := A.property a
      exact ⟨∅, t, unitGSet_supports _, ht, Finset.disjoint_empty_left t⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The left unitor `𝟙ₙ ⊗ₙ A ≅ A`. -/
def sepLeftUnitor (A : Nom) : 𝟙ₙ ⊗ₙ A ≅ A :=
  ObjectProperty.isoMk _
    (Action.mkIso (Equiv.toIso (sepLeftUnitorEquiv A)) (by intro π; ext p; rfl))

/-- Underlying bijection of the right unitor `A ⊗ₙ 𝟙ₙ ≅ A`. -/
def sepRightUnitorEquiv (A : Nom) : sepCarrier A.obj unitGSet ≃ A.obj.V where
  toFun p := p.1.1
  invFun a :=
    ⟨(a, PUnit.unit), by
      obtain ⟨t, ht⟩ := A.property a
      exact ⟨t, ∅, ht, unitGSet_supports _, Finset.disjoint_empty_right t⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The right unitor `A ⊗ₙ 𝟙ₙ ≅ A`. -/
def sepRightUnitor (A : Nom) : A ⊗ₙ 𝟙ₙ ≅ A :=
  ObjectProperty.isoMk _
    (Action.mkIso (Equiv.toIso (sepRightUnitorEquiv A)) (by intro π; ext p; rfl))

/-! ## Residuals — the associator, full monoidal typeclass, and M3

The pieces above (`sepObj`, `sepHom` with `sepHom_id`/`sepHom_comp`, `sepBraiding`,
`sepLeftUnitor`, `sepRightUnitor`) are the *core* of the separated-product monoidal structure and
are all genuine, non-vacuous isomorphisms/functorial data in `Nom`. Deliberately **not** provided
(to avoid a vacuous instance):

### The associator `(A ⊗ₙ B) ⊗ₙ C ≅ A ⊗ₙ (B ⊗ₙ C)`

The underlying reassociation bijection `((a, b), c) ↦ (a, (b, c))` is transparent, but showing it
is *well defined between the separated carriers* requires transporting the disjoint-support side
conditions: from `Separated A B a b` and `Separated (A ⊗ₙ B) C (a, b) c` one must derive
`Separated B C b c` and `Separated A (B ⊗ₙ C) a (b, c)` (and back).

With the existential `Separated` (∃ disjoint supporting sets) this transport does **not** go
through by recombining witnesses: `sepGSet_supports_fst`/`snd` give that an outer support of
`(a, b)` supports `a` and `b`, but building `Separated A (B ⊗ₙ C) a (b, c)` needs a support of `a`
*disjoint from* a support of `(b, c) = supp b ∪ supp c`, and the available witnesses overlap.

The honest fix is the classical **least-support** theory: the missing lemma is that finite
supports are closed under intersection —
`Supports X s x → Supports X t x → Supports X (s ∩ t) x` —
from which `supp x := ⋂ {s | Supports X s x}` is itself a support (the *least* support), and then
`supp (a, b) = supp a ∪ supp b` and `Separated a b ↔ Disjoint (supp a) (supp b)`. These make the
side-condition transport (hence the associator, its naturality, pentagon, and triangle) routine.
The intersection lemma is the standard nontrivial nominal-sets result (a fresh-atom interpolation
argument); it is the single identified prerequisite and is left as a precise residual.

### Full `MonoidalCategory Nom` / `SymmetricCategory Nom`

Gated on the associator above, plus the coherence obligations (pentagon, triangle; hexagon for
symmetry) and the whiskering/naturality fields of the `MonoidalCategory` typeclass. No instance is
registered here.

### M3 — monoidal closure `A ⊸ B` (not reached)

The fresh function space `A ⊸ B` (finitely-supported equivariant-up-to-support functions
`A.V → B.V`) and the currying adjunction `Nom(A ⊗ₙ B, C) ≃ Nom(A, B ⊸ C)` were not attempted;
they build on the least-support theory above (the support of a function, and freshness of the
argument) and on the completed monoidal structure. -/

end Nominal

