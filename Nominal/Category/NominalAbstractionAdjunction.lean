/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.Nominal
import Nominal.Category.NominalAbstraction
import Nominal.Category.NominalMonoidal
import Mathlib.CategoryTheory.Adjunction.Basic

set_option autoImplicit false

/-!
# The binding adjunction `(𝔸 ⊗ₙ −) ⊣ [𝔸](−)` on `Nom`

This file proves the **binding adjunction** of nominal sets (Pitts, *Nominal Sets*, §4.3–4.4):
the separated product with the atom object `𝔸` is left adjoint to atom-abstraction,
`(𝔸 ⊗ₙ −) ⊣ [𝔸](−)`, on the categorical nominal category `Nom`.

It is built on the least-support theory of `CatCrypt.Category.NominalMonoidal` (`supp`,
`supp_supports`, `supp_le`, `supports_inter`, `Separated_iff_disjoint`) and the abstraction
functor `absF` of `CatCrypt.Category.NominalAbstraction`.

## STEP 1 — concretion (the counit)

`concretize X : (𝔸 ⊗ₙ [𝔸]X) ⟶ X` opens an abstraction at a fresh atom:
on a separated pair `(a, ⟦(b, x)⟧)` (the separation gives `a # ⟦(b, x)⟧`) it returns
`swap a b • x`. This closes the residual left open in `NominalAbstraction` ("Residual:
concretion"): well-definedness on the `AbsRel` quotient at the *given* atom `a` genuinely
requires freshness (it fails for non-fresh `a`), which the least-support theory supplies.

The load-bearing lemmas are:

* `supp_smul` — equivariance of the least support, `supp (π • x) = (supp x).image π`;
* `fresh_abs` — if `a` is fresh for `⟦(b, x)⟧` and `a ≠ b` then `a` is fresh for `x`
  (the reverse support-shrink inclusion, proved by a fresh-atom swap argument);
* `concValue_absPt` — the computation rule `concValue a ⟦(b, x)⟧ = swap a b • x` for fresh `a`;
* `concValue_equivariant` — equivariance of concretion, hence `concretize` is an `Action.Hom`.

## STEP 2 — the unit

`unitHom A : A ⟶ [𝔸](𝔸 ⊗ₙ A)` sends `x` to `⟦(a, (a, x))⟧` for a fresh `a`; well-definedness
(independence of the chosen fresh atom) is `absPt_rename`, and equivariance is direct.

## STEP 3 — the hom-set bijection and the adjunction

`homEquiv A B : (𝔸 ⊗ₙ A ⟶ B) ≃ (A ⟶ absF.obj B)`, with the transpose of `f` given by
`unit ≫ absF.map f` and the inverse transpose of `g` given by `(𝔸 ◁ g) ≫ concretize`.  Both
triangle-like identities (`homEquiv_left_inv`, `homEquiv_right_inv`) are proved via the
computation/reconstruction rules `concValue_absPt` and `absPt_concValue`.

The naturality squares in `A` and `B` hold definitionally, so the bijection assembles into the
full adjunction `bindingAdjunction : MonoidalCategory.tensorLeft atomObj ⊣ absF`, i.e.
`(𝔸 ⊗ₙ −) ⊣ [𝔸](−)`, via `Adjunction.mkOfHomEquiv`.

Everything here is axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

open scoped Classical

namespace Nominal

/-! ## STEP 1 — concretion -/

variable {X : GSet}

/-- Injectivity of the abstraction point in its body, for a fixed head atom:
`⟦(a, y)⟧ = ⟦(a, y')⟧ → y = y'`. -/
lemma absPt_inj_body {a : Atom} {y y' : X.V} (h : absPt X a y = absPt X a y') : y = y' := by
  have hrel : AbsRel X (a, y) (a, y') := Quotient.exact h
  obtain ⟨s, hs⟩ := hrel
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset s
  have e : X.act (Equiv.swap a c) y = X.act (Equiv.swap a c) y' := hs c hc
  have e2 : X.act (Equiv.swap a c) (X.act (Equiv.swap a c) y)
      = X.act (Equiv.swap a c) (X.act (Equiv.swap a c) y') := by rw [e]
  rwa [← GSet.act_mul, ← GSet.act_mul, Equiv.swap_mul_self, GSet.act_one, GSet.act_one] at e2

/-- One inclusion of least-support equivariance. -/
lemma supp_smul_subset {A : GSet} (hA : IsNominal A) (π : PermAtom) (x : A.V) :
    supp hA (A.act π x) ⊆ (supp hA x).image π :=
  supp_le hA ((supp_supports hA x).smul π)

/-- **Equivariance of the least support**: `supp (π • x) = π • (supp x)`. -/
lemma supp_smul {A : GSet} (hA : IsNominal A) (π : PermAtom) (x : A.V) :
    supp hA (A.act π x) = (supp hA x).image π := by
  apply Finset.Subset.antisymm (supp_smul_subset hA π x)
  have h1 := supp_smul_subset hA π⁻¹ (A.act π x)
  rw [← GSet.act_mul, inv_mul_cancel, GSet.act_one] at h1
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hz' := h1 hz
  rw [Finset.mem_image] at hz'
  obtain ⟨w, hw, hwz⟩ := hz'
  have : (π : Atom → Atom) z = w := by rw [← hwz]; simp
  rw [this]; exact hw

/-- Computation of the atom-object action. -/
@[simp] lemma atomGSet_ρ_apply (π : PermAtom) (a : Atom) : atomGSet.act π a = π a := rfl

/-- Computation of the separated-product action on an explicit pair. -/
@[simp] lemma sepGSet_ρ_mk {A B : GSet} (π : PermAtom) (a : A.V) (b : B.V)
    (h : Separated A B a b) :
    (sepGSet A B).act π ⟨(a, b), h⟩ = ⟨(A.act π a, B.act π b), h.smul π⟩ := rfl

/-- An atom in the support of an atom-object element belongs to any of its finite supports. -/
lemma atom_mem_of_supports {s : Finset Atom} {a : Atom}
    (h : Supports atomGSet s a) : a ∈ s := by
  by_contra ha
  obtain ⟨e, he⟩ := Infinite.exists_notMem_finset (insert a s)
  simp only [Finset.mem_insert, not_or] at he
  obtain ⟨hea, hes⟩ := he
  have hfix : atomGSet.act (Equiv.swap a e) a = a :=
    h _ (fun d hd => Equiv.swap_apply_of_ne_of_ne
      (fun h' => ha (h' ▸ hd)) (fun h' => hes (h' ▸ hd)))
  rw [show atomGSet.act (Equiv.swap a e) a = Equiv.swap a e a from rfl, Equiv.swap_apply_left] at hfix
  exact hea hfix

/-- Freshness of the head atom for a separated pair `(a, y)` in `𝔸 ⊗ₙ Y`: `a` is fresh for `y`. -/
lemma fresh_of_sep {Y : GSet} (hY : IsNominal Y) {a : Atom} {y : Y.V}
    (h : Separated atomGSet Y a y) : a ∉ supp hY y := by
  obtain ⟨s, t, hs, ht, hd⟩ := h
  have has : a ∈ s := atom_mem_of_supports hs
  have hat : a ∉ t := Finset.disjoint_left.mp hd has
  exact fun hmem => hat (supp_le _ ht hmem)

/-- Freshness is preserved by an equivariant map: if `a` is fresh for `x` it is fresh for `f x`. -/
lemma fresh_map {A B : GSet} (hA : IsNominal A) (hB : IsNominal B) (f : A ⟶ B) {a : Atom}
    {x : A.V} (h : a ∉ supp hA x) : a ∉ supp hB (f.hom x) :=
  fun hmem => h (supp_le hB (Supports.map f (supp_supports hA x)) hmem)

/-- **Reverse support-shrink**: if `a` is fresh for the class `⟦(b, x)⟧` and `a ≠ b`, then `a`
is fresh for the body `x`.  Proved by a fresh-atom swap argument plus `supp_smul`. -/
lemma fresh_abs {hX : IsNominal X} {a b : Atom} {x : X.V}
    (hfresh : a ∉ supp (absGSet_isNominal hX) (absPt X b x)) (hab : a ≠ b) :
    a ∉ supp hX x := by
  intro hax
  have hcls : Supports (absGSet X) (supp (absGSet_isNominal hX) (absPt X b x)) (absPt X b x) :=
    supp_supports _ _
  obtain ⟨e, he⟩ := Infinite.exists_notMem_finset
    (supp (absGSet_isNominal hX) (absPt X b x) ∪ supp hX x ∪ {a, b})
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at he
  obtain ⟨⟨heScls, hesupp⟩, hea, heb⟩ := he
  have hswap_fix : (absGSet X).act (Equiv.swap a e) (absPt X b x) = absPt X b x := by
    apply hcls
    intro d hd
    exact Equiv.swap_apply_of_ne_of_ne (fun h' => hfresh (h' ▸ hd)) (fun h' => heScls (h' ▸ hd))
  rw [absGSet_ρ_mk, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm heb)] at hswap_fix
  have hxx : X.act (Equiv.swap a e) x = x := absPt_inj_body hswap_fix
  have hsupp_eq : supp hX x = (supp hX x).image (Equiv.swap a e) := by
    conv_lhs => rw [← hxx]
    rw [supp_smul hX (Equiv.swap a e) x]
  have hemem : e ∈ supp hX x := by
    rw [hsupp_eq, Finset.mem_image]
    exact ⟨a, hax, Equiv.swap_apply_left a e⟩
  exact hesupp hemem

/-- Concretion witness law: for fresh `a`, abstracting `swap a b • x` at `a` recovers `⟦(b, x)⟧`. -/
lemma absPt_swap_eq {hX : IsNominal X} {a b : Atom} {x : X.V}
    (hfresh : a ∉ supp (absGSet_isNominal hX) (absPt X b x)) :
    absPt X a (X.act (Equiv.swap a b) x) = absPt X b x := by
  by_cases hab : a = b
  · subst hab
    rw [show (Equiv.swap a a : PermAtom) = 1 from Equiv.swap_self a, GSet.act_one]
  · have hax := fresh_abs (hX := hX) hfresh hab
    have hrn := absPt_rename (X := X) (s := supp hX x) (a := b) (b := a) (x := x)
      (supp_supports hX x) hax hab
    rw [Equiv.swap_comm b a] at hrn
    exact hrn.symm

/-- **Concretion value** on the abstraction quotient: `concValue a q` is the (unique) body of `q`
when opened at `a`.  Defined totally via choice; the computation rule `concValue_absPt` holds when
`a` is fresh for `q`. -/
noncomputable def concValue (a : Atom) (q : (absGSet X).V) : X.V :=
  if h : ∃ y : X.V, absPt X a y = q then h.choose else (Quotient.out q).2

/-- **Computation rule** for concretion: for fresh `a`, `concValue a ⟦(b, x)⟧ = swap a b • x`. -/
lemma concValue_absPt {hX : IsNominal X} {a b : Atom} {x : X.V}
    (hfresh : a ∉ supp (absGSet_isNominal hX) (absPt X b x)) :
    concValue a (absPt X b x) = X.act (Equiv.swap a b) x := by
  have hex : ∃ y : X.V, absPt X a y = absPt X b x := ⟨_, absPt_swap_eq (hX := hX) hfresh⟩
  rw [concValue, dif_pos hex]
  exact absPt_inj_body (hex.choose_spec.trans (absPt_swap_eq (hX := hX) hfresh).symm)

/-- **Equivariance of concretion** on fresh pairs. -/
lemma concValue_equivariant {hX : IsNominal X} (π : PermAtom) {a : Atom} {q : (absGSet X).V}
    (hfresh : a ∉ supp (absGSet_isNominal hX) q) :
    concValue (π a) ((absGSet X).act π q) = X.act π (concValue a q) := by
  induction q using Quotient.inductionOn with
  | _ p =>
    obtain ⟨b, x⟩ := p
    have hfresh' : (π a) ∉ supp (absGSet_isNominal hX) ((absGSet X).act π (absPt X b x)) := by
      rw [supp_smul (absGSet_isNominal hX) π (absPt X b x), Finset.mem_image]
      rintro ⟨c, hc, hceq⟩
      exact hfresh (π.injective hceq ▸ hc)
    show concValue (π a) ((absGSet X).act π (absPt X b x))
      = X.act π (concValue a (absPt X b x))
    rw [absGSet_ρ_mk, concValue_absPt (hX := hX) hfresh', concValue_absPt (hX := hX) hfresh,
      ← GSet.act_mul, ← GSet.act_mul, swap_mul_perm]

/-- **Reconstruction rule**: abstracting the concretion at a fresh atom recovers the class. -/
lemma absPt_concValue {hX : IsNominal X} {a : Atom} {q : (absGSet X).V}
    (hfresh : a ∉ supp (absGSet_isNominal hX) q) :
    absPt X a (concValue a q) = q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    obtain ⟨b, x⟩ := p
    show absPt X a (concValue a (absPt X b x)) = absPt X b x
    rw [concValue_absPt (hX := hX) hfresh]
    exact absPt_swap_eq (hX := hX) hfresh

/-- The underlying `GSet` morphism of concretion. -/
noncomputable def concretizeHom (X : Nom) :
    sepGSet atomGSet (absGSet X.obj) ⟶ X.obj where
  hom := TypeCat.ofHom (fun p => concValue p.1.1 p.1.2)
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro p
    show concValue (π p.1.1) ((absGSet X.obj).act π p.1.2) = X.obj.act π (concValue p.1.1 p.1.2)
    exact concValue_equivariant (hX := X.property) π
      (fresh_of_sep (absGSet_isNominal X.property) p.2)

/-- **Concretion (the counit)** `𝔸 ⊗ₙ [𝔸]X ⟶ X`: opening an abstraction at a fresh atom. -/
noncomputable def concretize (X : Nom) : (atomObj ⊗ₙ absObj X) ⟶ X :=
  ObjectProperty.homMk (concretizeHom X)

/-! ## STEP 2 — the unit -/

/-- A fresh atom for `x`, chosen outside the least support of `x`. -/
noncomputable def freshFor (A : Nom) (x : A.obj.V) : Atom :=
  (Infinite.exists_notMem_finset (supp A.property x)).choose

lemma freshFor_spec (A : Nom) (x : A.obj.V) : freshFor A x ∉ supp A.property x :=
  (Infinite.exists_notMem_finset (supp A.property x)).choose_spec

/-- A fresh atom is separated from the element it is fresh for. -/
lemma sep_atom_of_fresh {A : Nom} {a : Atom} {x : A.obj.V} (h : a ∉ supp A.property x) :
    Separated atomGSet A.obj a x :=
  ⟨{a}, supp A.property x, (fun _ hπ => hπ a (Finset.mem_singleton_self a)),
    supp_supports A.property x, Finset.disjoint_singleton_left.mpr h⟩

/-- **The unit value** `η x = ⟦(a, (a, x))⟧` for a fresh atom `a`. -/
noncomputable def unitVal (A : Nom) (x : A.obj.V) :
    (absGSet (sepGSet atomGSet A.obj)).V :=
  absPt (sepGSet atomGSet A.obj) (freshFor A x)
    ⟨(freshFor A x, x), sep_atom_of_fresh (freshFor_spec A x)⟩

/-- Independence of the abstraction of `(a, x)` from the choice of fresh atom `a`. -/
lemma unitPt_indep {A : Nom} {a a' : Atom} {x : A.obj.V}
    (h : a ∉ supp A.property x) (h' : a' ∉ supp A.property x) :
    absPt (sepGSet atomGSet A.obj) a ⟨(a, x), sep_atom_of_fresh h⟩
      = absPt (sepGSet atomGSet A.obj) a' ⟨(a', x), sep_atom_of_fresh h'⟩ := by
  by_cases haa : a = a'
  · subst haa; rfl
  · have hp : Supports (sepGSet atomGSet A.obj) ({a} ∪ supp A.property x)
        ⟨(a, x), sep_atom_of_fresh h⟩ :=
      sepGSet_supports_pair (sep_atom_of_fresh h)
        (fun _ hπ => hπ a (Finset.mem_singleton_self a)) (supp_supports A.property x)
    have ha'ns : a' ∉ ({a} ∪ supp A.property x) := by
      simp only [Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨fun he => haa he.symm, h'⟩
    have hrn := absPt_rename (X := sepGSet atomGSet A.obj) (s := {a} ∪ supp A.property x)
      (a := a) (b := a') (x := ⟨(a, x), sep_atom_of_fresh h⟩) hp ha'ns (fun he => haa he.symm)
    rw [hrn]
    have hpair : (sepGSet atomGSet A.obj).act (Equiv.swap a a') ⟨(a, x), sep_atom_of_fresh h⟩
        = (⟨(a', x), sep_atom_of_fresh h'⟩ : sepCarrier atomGSet A.obj) := by
      apply Subtype.ext
      show (Equiv.swap a a' a, A.obj.act (Equiv.swap a a') x) = (a', x)
      rw [Equiv.swap_apply_left, swap_apply_eq_self (supp_supports A.property x) h h']
    rw [hpair]

/-- Computation rule for the unit: `η x = ⟦(a, (a, x))⟧` for any fresh `a`. -/
lemma unitVal_eq {A : Nom} {a : Atom} {x : A.obj.V} (h : a ∉ supp A.property x) :
    unitVal A x = absPt (sepGSet atomGSet A.obj) a ⟨(a, x), sep_atom_of_fresh h⟩ :=
  unitPt_indep (freshFor_spec A x) h

/-- **Equivariance of the unit.** -/
lemma unitVal_equivariant {A : Nom} (π : PermAtom) (x : A.obj.V) :
    (absGSet (sepGSet atomGSet A.obj)).act π (unitVal A x) = unitVal A (A.obj.act π x) := by
  have hfx := freshFor_spec A x
  rw [unitVal_eq hfx, absGSet_ρ_mk]
  have hπfresh : (π (freshFor A x)) ∉ supp A.property (A.obj.act π x) := by
    rw [supp_smul A.property π x, Finset.mem_image]
    rintro ⟨c, hc, hceq⟩
    exact hfx (π.injective hceq ▸ hc)
  rw [unitVal_eq hπfresh]
  have hpair : (sepGSet atomGSet A.obj).act π ⟨(freshFor A x, x), sep_atom_of_fresh hfx⟩
      = (⟨(π (freshFor A x), A.obj.act π x), sep_atom_of_fresh hπfresh⟩ : sepCarrier atomGSet A.obj) := by
    apply Subtype.ext; rfl
  rw [hpair]

/-- The underlying `GSet` morphism of the unit. -/
noncomputable def unitHom (A : Nom) : A.obj ⟶ absGSet (sepGSet atomGSet A.obj) where
  hom := TypeCat.ofHom (unitVal A)
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro x
    show unitVal A (A.obj.act π x) = (absGSet (sepGSet atomGSet A.obj)).act π (unitVal A x)
    exact (unitVal_equivariant π x).symm

/-- **The unit** `η A : A ⟶ [𝔸](𝔸 ⊗ₙ A)` of the binding adjunction. -/
noncomputable def unit (A : Nom) : A ⟶ absObj (atomObj ⊗ₙ A) :=
  ObjectProperty.homMk (unitHom A)

/-! ## STEP 3 — the hom-set bijection -/

open scoped MonoidalCategory

/-- **Forward transpose** `(𝔸 ⊗ₙ A ⟶ B) → (A ⟶ [𝔸]B)`, given by `η ≫ [𝔸]f`. -/
noncomputable def homEquivToFun (A B : Nom) (f : (atomObj ⊗ₙ A) ⟶ B) :
    A ⟶ absF.obj B :=
  unit A ≫ absF.map f

/-- **Inverse transpose** `(A ⟶ [𝔸]B) → (𝔸 ⊗ₙ A ⟶ B)`, given by `(𝔸 ◁ g) ≫ ε`. -/
noncomputable def homEquivInvFun (A B : Nom) (g : A ⟶ absF.obj B) :
    (atomObj ⊗ₙ A) ⟶ B :=
  MonoidalCategory.whiskerLeft atomObj g ≫ concretize B

/-- Element-level reduction of the forward transpose. -/
lemma homEquivToFun_apply (A B : Nom) (f : (atomObj ⊗ₙ A) ⟶ B) (x : A.obj.V) :
    (homEquivToFun A B f).hom.hom x
      = absPt B.obj (freshFor A x)
          (f.hom.hom ⟨(freshFor A x, x), sep_atom_of_fresh (freshFor_spec A x)⟩) := rfl

/-- Element-level reduction of the inverse transpose. -/
lemma homEquivInvFun_apply (A B : Nom) (g : A ⟶ absF.obj B) (p : sepCarrier atomGSet A.obj) :
    (homEquivInvFun A B g).hom.hom p = concValue p.1.1 (g.hom.hom p.1.2) := rfl

/-- `toFun ∘ invFun = id`. -/
lemma homEquiv_right_inv (A B : Nom) (g : A ⟶ absF.obj B) :
    homEquivToFun A B (homEquivInvFun A B g) = g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext; intro x
  rw [homEquivToFun_apply, homEquivInvFun_apply]
  exact absPt_concValue (hX := B.property)
    (fresh_map A.property (absGSet_isNominal B.property) g.hom (freshFor_spec A x))

/-- Pointwise form of `invFun ∘ toFun = id` (with `p` at the `atomGSet` separated carrier). -/
lemma homEquiv_left_inv_apply (A B : Nom) (f : (atomObj ⊗ₙ A) ⟶ B)
    (p : sepCarrier atomGSet A.obj) :
    (homEquivInvFun A B (homEquivToFun A B f)).hom.hom p = f.hom.hom p := by
  obtain ⟨⟨a, x⟩, hsep⟩ := p
  rw [homEquivInvFun_apply, homEquivToFun_apply]
  have hax : a ∉ supp A.property x := fresh_of_sep A.property hsep
  have ha0x : freshFor A x ∉ supp A.property x := freshFor_spec A x
  have hz_supp : Supports B.obj ({freshFor A x} ∪ supp A.property x)
      (f.hom.hom ⟨(freshFor A x, x), sep_atom_of_fresh (freshFor_spec A x)⟩) :=
    Supports.map f.hom (sepGSet_supports_pair (sep_atom_of_fresh (freshFor_spec A x))
      (fun _ hπ => hπ (freshFor A x) (Finset.mem_singleton_self _)) (supp_supports A.property x))
  have hfresh_a : a ∉ supp (absGSet_isNominal B.property)
      (absPt B.obj (freshFor A x)
        (f.hom.hom ⟨(freshFor A x, x), sep_atom_of_fresh (freshFor_spec A x)⟩)) := by
    intro hmem
    have hmem2 := supp_le (absGSet_isNominal B.property) (absGSet_supports hz_supp) hmem
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton] at hmem2
    rcases hmem2.1 with h1 | h2
    · exact hmem2.2 h1
    · exact hax h2
  rw [concValue_absPt (hX := B.property) hfresh_a]
  have hcomm : f.hom.hom ((sepGSet atomGSet A.obj).act (Equiv.swap a (freshFor A x))
        ⟨(freshFor A x, x), sep_atom_of_fresh (freshFor_spec A x)⟩)
      = B.obj.act (Equiv.swap a (freshFor A x))
        (f.hom.hom ⟨(freshFor A x, x), sep_atom_of_fresh (freshFor_spec A x)⟩) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (f.hom.comm (Equiv.swap a (freshFor A x)))
        ⟨(freshFor A x, x), sep_atom_of_fresh (freshFor_spec A x)⟩
  rw [← hcomm]
  have hwpair : (sepGSet atomGSet A.obj).act (Equiv.swap a (freshFor A x))
        ⟨(freshFor A x, x), sep_atom_of_fresh (freshFor_spec A x)⟩
      = (⟨(a, x), hsep⟩ : sepCarrier atomGSet A.obj) := by
    rw [sepGSet_ρ_mk]
    apply Subtype.ext
    show (atomGSet.act (Equiv.swap a (freshFor A x)) (freshFor A x),
      A.obj.act (Equiv.swap a (freshFor A x)) x) = (a, x)
    rw [atomGSet_ρ_apply, Equiv.swap_apply_right,
      swap_apply_eq_self (supp_supports A.property x) hax ha0x]
  rw [hwpair]

/-- `invFun ∘ toFun = id`. -/
lemma homEquiv_left_inv (A B : Nom) (f : (atomObj ⊗ₙ A) ⟶ B) :
    homEquivInvFun A B (homEquivToFun A B f) = f := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext; intro p
  exact homEquiv_left_inv_apply A B f p

/-- **The binding hom-set bijection** `(𝔸 ⊗ₙ A ⟶ B) ≃ (A ⟶ [𝔸]B)`. -/
noncomputable def homEquiv (A B : Nom) : ((atomObj ⊗ₙ A) ⟶ B) ≃ (A ⟶ absF.obj B) where
  toFun := homEquivToFun A B
  invFun := homEquivInvFun A B
  left_inv := homEquiv_left_inv A B
  right_inv := homEquiv_right_inv A B

/-- **The binding adjunction** `(𝔸 ⊗ₙ −) ⊣ [𝔸](−)` (Pitts, *Nominal Sets* §4.3–4.4):
separated product with the atom object is left adjoint to atom abstraction. -/
noncomputable def bindingAdjunction : MonoidalCategory.tensorLeft atomObj ⊣ absF :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B => homEquiv A B
      homEquiv_naturality_left_symm := by
        intro A' A B f g
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext; intro p
        rfl
      homEquiv_naturality_right := by
        intro A B B' f g
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext; intro x
        rfl }

end Nominal
