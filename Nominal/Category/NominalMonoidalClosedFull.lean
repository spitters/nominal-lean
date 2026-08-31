/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.NominalMonoidalClosed

set_option autoImplicit false

/-!
# M3, part 2 — the determined-by-fresh theory and the exponential obstruction

This file continues `CatCrypt.Category.NominalMonoidalClosed` toward monoidal closure of `Nom`
for the separated product `⊗ₙ`.  It proves the genuine **determined-by-fresh-values** lemmas that
the internal-hom development rests on, and then pins down *precisely* why the naive internal hom
`funObj` (total finitely-supported functions) does **not** carry a `MonoidalClosed Nom` structure
for the separated product.

## What is proved

* `funGSetFull_recover` / `funGSetFull_recover_welldef` — the determined-by-fresh recovery:
  a function supported by `s` has `f b = C.ρ π⁻¹ (f (B.ρ π b))` for every `π` fixing `s`, so the
  recovered value is independent of the support-fixing permutation used.
* `curry_sep_transport` — the separated-value assignment `b ↦ g ⟨(a, b), _⟩` of a morphism
  `g : A ⊗ₙ B ⟶ C` is supported by `supp a`: for `π` fixing `supp a` it intertwines the actions.
  This is the equivariance that a curried transpose must satisfy on the fresh locus.
* `uncurry_not_injective` — the **obstruction**: with the total-function internal hom `funObj`, the
  transpose map `uncurry : (A ⟶ B ⊸ₙ C) → (A ⊗ₙ B ⟶ C)` is not injective.  Hence it is not a
  bijection and `funObj` cannot be the right adjoint of `· ⊗ₙ B`; no `MonoidalClosed Nom` instance
  is (or can be) registered with this internal hom.

## Why `MonoidalClosed Nom` is not registered here

For the *cartesian* product `Nom` is cartesian closed with internal hom exactly `funObj` (total
finitely-supported functions under conjugation).  The monoidal structure registered on `Nom`
(`instMonoidalNom`) is the *separated* product `⊗ₙ`, whose right adjoint is a strictly smaller
object — the **separated (fresh) function space** consisting of functions determined by their
values on *fresh* arguments only.  `uncurry_not_injective` witnesses the gap concretely: two
distinct morphisms into `funObj` that agree on all separated pairs, hence have equal uncurryings.
Registering `Closed B` / `MonoidalClosed Nom` with `funObj` would require an inverse to a
non-injective map, so it is impossible — not merely unproved.  The precise residual is therefore
"replace `funObj` by the separated function space", documented at the end of this file.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

open scoped Classical

namespace Nominal

/-! ## The determined-by-fresh recovery -/

/-- **Determined-by-fresh recovery.**  A finitely supported function supported by `s` recovers its
value at `b` from its value at any support-fixing translate `B.ρ π b`:
`f b = C.ρ π⁻¹ (f (B.ρ π b))` whenever `π` fixes `s` pointwise.  This is
`funGSetFull_apply_of_supports` solved for `f b`. -/
lemma funGSetFull_recover {B C : GSet} {s : Finset Atom} {f : B.V → C.V}
    (hf : Supports (funGSetFull B C) s f) {π : PermAtom} (hπ : ∀ a ∈ s, π a = a) (b : B.V) :
    f b = C.act π⁻¹ (f (B.act π b)) := by
  have h := funGSetFull_apply_of_supports hf hπ b
  rw [h, ← GSet.act_mul, inv_mul_cancel, GSet.act_one]

/-- The recovered value does not depend on the chosen support-fixing permutation: any two
permutations fixing a support `s` of `f` recover the same value at `b`. -/
lemma funGSetFull_recover_welldef {B C : GSet} {s : Finset Atom} {f : B.V → C.V}
    (hf : Supports (funGSetFull B C) s f) {π₁ π₂ : PermAtom}
    (h₁ : ∀ a ∈ s, π₁ a = a) (h₂ : ∀ a ∈ s, π₂ a = a) (b : B.V) :
    C.act π₁⁻¹ (f (B.act π₁ b)) = C.act π₂⁻¹ (f (B.act π₂ b)) := by
  rw [← funGSetFull_recover hf h₁ b, ← funGSetFull_recover hf h₂ b]

/-! ## The separated-value assignment is supported by `supp a` -/

/-- **Support-transport of the separated values.**  For `g : A ⊗ₙ B ⟶ C` and any `a`, the partial
function `b ↦ g ⟨(a, b), _⟩` (defined on `b` separated from `a`) is supported by `supp a`: a
permutation `π` fixing `supp a` intertwines it with the action on `C`.  This is exactly the
equivariance a curried transpose must satisfy on the fresh locus. -/
lemma curry_sep_transport {A B C : Nom} (g : A ⊗ₙ B ⟶ C) (a : A.obj.V)
    {π : PermAtom} (hπ : ∀ x ∈ supp A.property a, π x = x)
    {b : B.obj.V} (hsep : Separated A.obj B.obj a b)
    (hsep' : Separated A.obj B.obj a (B.obj.act π b)) :
    g.hom.hom ⟨(a, B.obj.act π b), hsep'⟩ = C.obj.act π (g.hom.hom ⟨(a, b), hsep⟩) := by
  have ha : A.obj.act π a = a := supp_supports A.property a π hπ
  have hc : g.hom.hom ((sepGSet A.obj B.obj).act π ⟨(a, b), hsep⟩)
      = C.obj.act π (g.hom.hom ⟨(a, b), hsep⟩) := by
    have := ConcreteCategory.congr_hom (g.hom.comm π) (⟨(a, b), hsep⟩ : sepCarrier A.obj B.obj)
    simpa only [ConcreteCategory.comp_apply] using! this
  rw [← hc]
  apply congrArg
  apply Subtype.ext
  show (a, B.obj.act π b) = (A.obj.act π a, B.obj.act π b)
  rw [ha]

/-! ## The obstruction: `uncurry` is not injective for the total-function internal hom

We now show, by a concrete counterexample, that with the total finitely-supported function space
`funObj` the transpose `uncurry : (A ⟶ B ⊸ₙ C) → (A ⊗ₙ B ⟶ C)` is **not injective**.  Two
morphisms `𝔸 ⟶ (𝔸 ⊸ₙ 𝟚)` that differ only on the *diagonal* (non-separated) arguments have equal
uncurryings, because uncurrying only ever inspects values on *separated* pairs.  Consequently
`uncurry` is not a bijection, `funObj` is not the right adjoint of `· ⊗ₙ B`, and no
`MonoidalClosed Nom` structure exists with this internal hom. -/

/-- Group-inverse cancellation as function application: `π (π⁻¹ x) = x`. -/
private lemma perm_apply_inv (π : PermAtom) (x : Atom) : π (π⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

/-- Group-inverse cancellation as function application: `π⁻¹ (π x) = x`. -/
private lemma perm_inv_apply (π : PermAtom) (x : Atom) : π⁻¹ (π x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

/-- Two atoms with a group-inverse: `π⁻¹ x = a ↔ x = π a`. -/
private lemma perm_inv_eq_iff (π : PermAtom) (x a : Atom) : (π⁻¹ x = a) ↔ (x = π a) := by
  constructor
  · intro h; rw [← h, perm_apply_inv]
  · intro h; rw [h, perm_inv_apply]

/-- A finite set supporting an atom (in `atomGSet`) must contain it. -/
private lemma atom_supports_mem {s : Finset Atom} {a : Atom} (h : Supports atomGSet s a) :
    a ∈ s := by
  by_contra ha
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (insert a s)
  rw [Finset.mem_insert, not_or] at hc
  obtain ⟨hca, hcs⟩ := hc
  have hfix : atomGSet.act (Equiv.swap a c) a = a :=
    h (Equiv.swap a c) (by
      intro e he
      exact Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ he)) (fun h => hcs (h ▸ he)))
  rw [show atomGSet.act (Equiv.swap a c) a = Equiv.swap a c a from rfl,
    Equiv.swap_apply_left] at hfix
  exact hca hfix

/-- Two `decide`s of equivalent propositions are equal (instance-agnostic). -/
private lemma decide_eq_of_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := decide_eq_decide.mpr h

/-- Separated atoms are distinct. -/
private lemma atom_separated_ne {a b : Atom} (h : Separated atomGSet atomGSet a b) : a ≠ b := by
  obtain ⟨s, t, hs, ht, hd⟩ := h
  intro hab
  subst hab
  exact (Finset.disjoint_left.mp hd (atom_supports_mem hs)) (atom_supports_mem ht)

/-- The two-point nominal set `𝟚` with the trivial action; both points are supported by `∅`. -/
def boolGSet : GSet := Action.trivial PermAtom Bool

@[simp] lemma boolGSet_ρ (π : PermAtom) (b : Bool) : boolGSet.act π b = b := rfl

@[simp] lemma atomGSet_ρ (π : PermAtom) (x : Atom) : atomGSet.act π x = π x := rfl

lemma boolGSet_isNominal : IsNominal boolGSet :=
  fun _ => ⟨∅, fun _ _ => rfl⟩

/-- `𝟚` as an object of `Nom`. -/
def boolObj : Nom := Nom.of boolGSet boolGSet_isNominal

/-- The indicator function `x ↦ (x = a)`, a finitely-supported function `𝔸 → 𝟚` supported by
`{a}`. -/
noncomputable def indicElt (a : Atom) : funCarrier atomGSet boolGSet :=
  ⟨fun x => decide (x = a), by
    refine ⟨{a}, ?_⟩
    intro π hπ
    funext x
    have hpa : π a = a := hπ a (Finset.mem_singleton_self a)
    simp only [funGSetFull_ρ, boolGSet_ρ, atomGSet_ρ]
    exact decide_eq_of_iff ((perm_inv_eq_iff π x a).trans (iff_of_eq (congrArg (x = ·) hpa)))⟩

/-- The constant-`false` function, supported by `∅`. -/
def constFalseElt : funCarrier atomGSet boolGSet :=
  ⟨fun _ => false, ⟨∅, fun _ _ => rfl⟩⟩

/-- Underlying equivariant map `𝔸 ⟶ (𝔸 ⊸ₙ 𝟚)` sending `a` to the indicator of `a`. -/
noncomputable def indicActionHom : atomObj.obj ⟶ (atomObj ⊸ₙ boolObj).obj where
  hom := TypeCat.ofHom indicElt
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro a
    apply Subtype.ext
    funext x
    show (indicElt (atomGSet.act π a)).1 x
      = (funGSetFull atomGSet boolGSet).act π (indicElt a).1 x
    simp only [funGSetFull_ρ, boolGSet_ρ, atomGSet_ρ, indicElt]
    refine decide_eq_of_iff ?_
    exact (perm_inv_eq_iff π x a).symm

/-- Underlying equivariant map `𝔸 ⟶ (𝔸 ⊸ₙ 𝟚)` sending everything to the constant-`false`
function. -/
def constFalseActionHom : atomObj.obj ⟶ (atomObj ⊸ₙ boolObj).obj where
  hom := TypeCat.ofHom fun _ => constFalseElt
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro a
    apply Subtype.ext
    funext x
    rfl

/-- First witness morphism `𝔸 ⟶ (𝔸 ⊸ₙ 𝟚)`: `a ↦ indicator of a`. -/
noncomputable def indicMor : atomObj ⟶ (atomObj ⊸ₙ boolObj) := ObjectProperty.homMk indicActionHom

/-- Second witness morphism `𝔸 ⟶ (𝔸 ⊸ₙ 𝟚)`: constantly the `false` function. -/
def constFalseMor : atomObj ⟶ (atomObj ⊸ₙ boolObj) := ObjectProperty.homMk constFalseActionHom

/-- The two witnesses agree after uncurrying: on a separated pair `(a, b)` we have `a ≠ b`, so the
indicator of `a` is `false` at `b`, matching the constant-`false` map. -/
lemma uncurry_indic_eq_constFalse : uncurry indicMor = uncurry constFalseMor := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro p
  simp only [uncurry_apply, indicMor, constFalseMor, ObjectProperty.homMk_hom, indicActionHom,
    constFalseActionHom, constFalseElt]
  exact decide_eq_false_iff_not.mpr (fun h => atom_separated_ne p.2 h.symm)

/-- But the two witnesses are distinct: they differ on the diagonal argument `(a, a)`, which
uncurrying never inspects — `indicMor 0` is `true` at `0` while `constFalseMor 0` is `false`. -/
lemma indicMor_ne_constFalse : indicMor ≠ constFalseMor := by
  intro heq
  have h := congrArg
    (fun m : atomObj ⟶ (atomObj ⊸ₙ boolObj) => (m.hom.hom (0 : Atom)).1 (0 : Atom)) heq
  simp only [indicMor, constFalseMor, ObjectProperty.homMk_hom, indicActionHom,
    constFalseActionHom, constFalseElt] at h
  simp [indicElt] at h

/-- **The obstruction.**  For the total finitely-supported function internal hom `funObj`, the
transpose `uncurry` is not injective: there exist distinct `h ≠ h' : 𝔸 ⟶ (𝔸 ⊸ₙ 𝟚)` with
`uncurry h = uncurry h'`.  Hence `uncurry` is not a bijection, `funObj` is not the right adjoint of
the separated tensor `· ⊗ₙ 𝔸`, and no `MonoidalClosed Nom` instance can be registered with this
internal hom. -/
theorem uncurry_not_injective :
    ∃ (A B C : Nom) (h h' : A ⟶ B ⊸ₙ C), uncurry h = uncurry h' ∧ h ≠ h' :=
  ⟨atomObj, atomObj, boolObj, indicMor, constFalseMor,
    uncurry_indic_eq_constFalse, indicMor_ne_constFalse⟩

/-! ## The precise residual

`uncurry_not_injective` is the exact obstruction to `MonoidalClosed Nom` for the separated product
with internal hom `funObj`:

* the total finitely-supported function space `funObj` is the *cartesian* internal hom (`Nom` is
  cartesian closed with exponential `funObj`), **not** the separated-tensor internal hom;
* the right adjoint of `· ⊗ₙ B` is the strictly smaller **separated (fresh) function space** — the
  subobject of `funObj` of functions determined by their values on arguments *fresh* for the
  function.  `uncurry_indic_eq_constFalse` / `indicMor_ne_constFalse` exhibit two elements of
  `funObj` with identical fresh restrictions but different diagonal values; the separated function
  space identifies exactly such pairs.

Therefore **no** `Closed B` / `MonoidalClosed Nom` instance is registered here.  Doing so with
`funObj` would require inverting the non-injective `uncurry`, which is impossible.  Closing M3
requires replacing `funObj` by the separated function space and redeveloping `evalHom`/`uncurry`
over it; the determined-by-fresh lemmas above (`funGSetFull_recover`,
`funGSetFull_recover_welldef`, `curry_sep_transport`) are the reusable nominal core of that
redevelopment. -/

end Nominal
