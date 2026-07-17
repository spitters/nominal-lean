/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.Nominal
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

set_option autoImplicit false

/-!
# Least-support theory and the separated-product monoidal structure on `Nom`

This file completes the separated-product (disjoint-support) monoidal structure on the category
`Nom` of nominal sets started in `CatCrypt.Category.Nominal`. It has three parts.

## STEP 1 — least-support theory

The crux is that finite supports are closed under intersection
(`supports_inter`), the classical nominal-sets result proved by a fresh-atom interpolation
argument (Pitts, *Nominal Sets*). From it we build the least support `supp x` (the intersection
of all supports), prove it *is* a support (`supp_supports`) and is contained in every support
(`supp_le`), and derive `supp_pair` (the support of a separated pair is the union of supports)
and `Separated_iff_disjoint` (separation is disjointness of least supports).

## STEP 2 — the associator and `MonoidalCategory Nom`

Using `Separated_iff_disjoint` the side-condition transport across reassociation becomes routine,
giving the associator `(A ⊗ₙ B) ⊗ₙ C ≅ A ⊗ₙ (B ⊗ₙ C)` and hence the full `MonoidalCategory` and
`SymmetricCategory` instances.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

open scoped Classical

namespace Nominal

/-! ## STEP 1 — least-support theory -/

/-- Upward closure of support: a superset of a support is a support. -/
lemma Supports.mono {A : GSet} {s s' : Finset Atom} {x : A.V}
    (h : Supports A s x) (hss : s ⊆ s') : Supports A s' x :=
  fun π hπ => h π (fun a ha => hπ a (hss ha))

/-- A permutation swapping two atoms both **outside** a support fixes the supported element. -/
lemma swap_apply_eq_self {A : GSet} {s : Finset Atom} {x : A.V}
    (hs : Supports A s x) {a b : Atom} (ha : a ∉ s) (hb : b ∉ s) :
    A.act (Equiv.swap a b) x = x := by
  apply hs
  intro e he
  have ea : e ≠ a := fun h => ha (h ▸ he)
  have eb : e ≠ b := fun h => hb (h ▸ he)
  exact Equiv.swap_apply_of_ne_of_ne ea eb

/-- **Erase step** for the intersection theorem: if `s` and `t` both support `x` and `a ∈ s`,
`a ∉ t`, then `x` is already supported by `s.erase a`. This is the single-atom fresh-renaming
move; iterating it over `s \ t` yields `supports_inter`. -/
lemma supports_erase {A : GSet} {s t : Finset Atom} {x : A.V}
    (hs : Supports A s x) (ht : Supports A t x) {a : Atom}
    (has : a ∈ s) (hat : a ∉ t) :
    Supports A (s.erase a) x := by
  intro π hπ
  set a' := π a with ha'def
  by_cases haa' : a' = a
  · -- `π` fixes all of `s`, so `Supports A s x` applies directly.
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
      exact haa' ((π.injective hpp).symm)
    -- `ζ := swap a a' * π` fixes `s`, so `ζ • x = x`; hence `π • x = swap a a' • x`.
    have hzeta : A.act (Equiv.swap a a' * π) x = x := by
      apply hs
      intro e he
      rw [Equiv.Perm.mul_apply]
      by_cases hea : e = a
      · subst hea; rw [← ha'def, Equiv.swap_apply_right]
      · have hpe : π e = e := hπ e (Finset.mem_erase.mpr ⟨hea, he⟩)
        rw [hpe]
        have hea' : e ≠ a' := fun h => ha'ns (h ▸ he)
        exact Equiv.swap_apply_of_ne_of_ne hea hea'
    have hinv : ∀ y : A.V, A.act (Equiv.swap a a') (A.act (Equiv.swap a a') y) = y := by
      intro y
      rw [← GSet.act_mul, Equiv.swap_mul_self, GSet.act_one]
    have hStepA : A.act π x = A.act (Equiv.swap a a') x := by
      have h0 : A.act (Equiv.swap a a') (A.act π x) = x := by
        rw [← GSet.act_mul]; exact hzeta
      have hkey := hinv (A.act π x)
      rw [h0] at hkey
      exact hkey.symm
    -- Fresh atom `c` outside `s ∪ t ∪ {a, a'}` breaks `swap a a'` into two support-fixing swaps.
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (s ∪ t ∪ {a, a'})
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨⟨hcs, hct⟩, hca, hca'⟩ := hc
    have hid : Equiv.swap a a'
        = Equiv.swap a c * Equiv.swap a' c * Equiv.swap a c := by
      have h := Equiv.swap_mul_swap_mul_swap (Ne.symm hca') haa'
      rw [Equiv.swap_comm c a] at h
      exact h.symm
    have hswap : A.act (Equiv.swap a a') x = x := by
      rw [hid, GSet.act_mul, GSet.act_mul,
        swap_apply_eq_self ht hat hct,
        swap_apply_eq_self hs ha'ns hcs,
        swap_apply_eq_self ht hat hct]
    rw [hStepA, hswap]

/-- Auxiliary for `supports_inter`: strong induction on `(s \ t).card`. -/
private lemma supports_inter_aux {A : GSet} {t : Finset Atom} {x : A.V}
    (ht : Supports A t x) :
    ∀ (n : ℕ) (s : Finset Atom), (s \ t).card = n → Supports A s x → Supports A (s ∩ t) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro s hcard hs
    rcases Finset.eq_empty_or_nonempty (s \ t) with hemp | ⟨a, ha⟩
    · rw [Finset.sdiff_eq_empty_iff_subset] at hemp
      rwa [Finset.inter_eq_left.mpr hemp]
    · rw [Finset.mem_sdiff] at ha
      obtain ⟨has, hat⟩ := ha
      have hstep : Supports A (s.erase a) x := supports_erase hs ht has hat
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

/-- **Finite supports are closed under intersection.** The classical least-support result. -/
lemma supports_inter {A : GSet} {s t : Finset Atom} {x : A.V}
    (hs : Supports A s x) (ht : Supports A t x) :
    Supports A (s ∩ t) x :=
  supports_inter_aux ht _ s rfl hs

/-! ### The least support -/

/-- The **least support** of an element of a nominal set: the intersection of all supporting
finite sets (realized as the `inf'` of the supporting subsets of one chosen support). -/
noncomputable def supp {A : GSet} (hA : IsNominal A) (x : A.V) : Finset Atom :=
  ((hA x).choose.powerset.filter (fun s => Supports A s x)).inf'
    ⟨(hA x).choose,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), (hA x).choose_spec⟩⟩ id

/-- The least support is a support. -/
lemma supp_supports {A : GSet} (hA : IsNominal A) (x : A.V) : Supports A (supp hA x) x := by
  unfold supp
  refine Finset.inf'_induction (p := fun r : Finset Atom => Supports A r x) _ id ?_ ?_
  · intro a₁ h₁ a₂ h₂
    show Supports A (a₁ ∩ a₂) x
    exact supports_inter h₁ h₂
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

/-- The least support is contained in every support. -/
lemma supp_le {A : GSet} (hA : IsNominal A) {x : A.V} {s : Finset Atom}
    (hsupp : Supports A s x) : supp hA x ⊆ s := by
  have hs0supp : Supports A (hA x).choose x := (hA x).choose_spec
  have hmem : s ∩ (hA x).choose ∈
      (hA x).choose.powerset.filter (fun u => Supports A u x) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, supports_inter hsupp hs0supp⟩
  have hle : supp hA x ⊆ s ∩ (hA x).choose := Finset.inf'_le (f := id) hmem
  exact hle.trans Finset.inter_subset_left

/-- The support of a separated pair is the union of the supports of its components. -/
lemma supp_pair {A B : GSet} (hA : IsNominal A) (hB : IsNominal B)
    {a : A.V} {b : B.V} (hsep : Separated A B a b) :
    supp (sepGSet_isNominal hA hB) (⟨(a, b), hsep⟩ : sepCarrier A B)
      = supp hA a ∪ supp hB b := by
  apply Finset.Subset.antisymm
  · exact supp_le (sepGSet_isNominal hA hB)
      (sepGSet_supports_pair hsep (supp_supports hA a) (supp_supports hB b))
  · apply Finset.union_subset
    · exact supp_le hA
        (sepGSet_supports_fst (supp_supports (sepGSet_isNominal hA hB) ⟨(a, b), hsep⟩))
    · exact supp_le hB
        (sepGSet_supports_snd (supp_supports (sepGSet_isNominal hA hB) ⟨(a, b), hsep⟩))

/-- Separation of two elements is exactly disjointness of their least supports. -/
lemma Separated_iff_disjoint {A B : GSet} (hA : IsNominal A) (hB : IsNominal B)
    (a : A.V) (b : B.V) :
    Separated A B a b ↔ Disjoint (supp hA a) (supp hB b) := by
  constructor
  · rintro ⟨s, t, hs, ht, hd⟩
    exact hd.mono (supp_le hA hs) (supp_le hB ht)
  · intro hd
    exact ⟨supp hA a, supp hB b, supp_supports hA a, supp_supports hB b, hd⟩

/-! ## STEP 2 — the associator and the monoidal structure

With `Separated_iff_disjoint` the side-condition transport across reassociation reduces to routine
`Disjoint`/`∪` manipulations on least supports. -/

section Associator

variable {A B C : Nom}

/-- Transport: the middle pair of a left-nested separated triple is separated. -/
lemma sep_bc {a : A.obj.V} {b : B.obj.V} {c : C.obj.V}
    (hab : Separated A.obj B.obj a b)
    (houter : Separated (sepGSet A.obj B.obj) C.obj ⟨(a, b), hab⟩ c) :
    Separated B.obj C.obj b c := by
  rw [Separated_iff_disjoint B.property C.property]
  have h1 := (Separated_iff_disjoint (sepGSet_isNominal A.property B.property) C.property
    ⟨(a, b), hab⟩ c).mp houter
  rw [supp_pair A.property B.property hab] at h1
  exact h1.mono_left Finset.subset_union_right

/-- Transport: reassociating a left-nested separated triple to the right stays separated. -/
lemma sep_a_bc {a : A.obj.V} {b : B.obj.V} {c : C.obj.V}
    (hab : Separated A.obj B.obj a b)
    (houter : Separated (sepGSet A.obj B.obj) C.obj ⟨(a, b), hab⟩ c) :
    Separated A.obj (sepGSet B.obj C.obj) a ⟨(b, c), sep_bc hab houter⟩ := by
  rw [Separated_iff_disjoint A.property (sepGSet_isNominal B.property C.property),
    supp_pair B.property C.property (sep_bc hab houter), Finset.disjoint_union_right]
  refine ⟨(Separated_iff_disjoint A.property B.property a b).mp hab, ?_⟩
  have h1 := (Separated_iff_disjoint (sepGSet_isNominal A.property B.property) C.property
    ⟨(a, b), hab⟩ c).mp houter
  rw [supp_pair A.property B.property hab] at h1
  exact h1.mono_left Finset.subset_union_left

/-- Transport: the outer pair of a right-nested separated triple is separated. -/
lemma sep_ab {a : A.obj.V} {b : B.obj.V} {c : C.obj.V}
    (hbc : Separated B.obj C.obj b c)
    (houter : Separated A.obj (sepGSet B.obj C.obj) a ⟨(b, c), hbc⟩) :
    Separated A.obj B.obj a b := by
  rw [Separated_iff_disjoint A.property B.property]
  have h1 := (Separated_iff_disjoint A.property (sepGSet_isNominal B.property C.property)
    a ⟨(b, c), hbc⟩).mp houter
  rw [supp_pair B.property C.property hbc] at h1
  exact h1.mono_right Finset.subset_union_left

/-- Transport: reassociating a right-nested separated triple to the left stays separated. -/
lemma sep_ab_c {a : A.obj.V} {b : B.obj.V} {c : C.obj.V}
    (hbc : Separated B.obj C.obj b c)
    (houter : Separated A.obj (sepGSet B.obj C.obj) a ⟨(b, c), hbc⟩) :
    Separated (sepGSet A.obj B.obj) C.obj ⟨(a, b), sep_ab hbc houter⟩ c := by
  rw [Separated_iff_disjoint (sepGSet_isNominal A.property B.property) C.property,
    supp_pair A.property B.property (sep_ab hbc houter), Finset.disjoint_union_left]
  refine ⟨?_, (Separated_iff_disjoint B.property C.property b c).mp hbc⟩
  have h1 := (Separated_iff_disjoint A.property (sepGSet_isNominal B.property C.property)
    a ⟨(b, c), hbc⟩).mp houter
  rw [supp_pair B.property C.property hbc] at h1
  exact h1.mono_right Finset.subset_union_right

/-- Forward reassociation on separated carriers `((a, b), c) ↦ (a, (b, c))`. -/
def sepAssocFwd (p : sepCarrier (sepGSet A.obj B.obj) C.obj) :
    sepCarrier A.obj (sepGSet B.obj C.obj) :=
  ⟨(p.1.1.1.1, ⟨(p.1.1.1.2, p.1.2), sep_bc p.1.1.2 p.2⟩), sep_a_bc p.1.1.2 p.2⟩

/-- Backward reassociation on separated carriers `(a, (b, c)) ↦ ((a, b), c)`. -/
def sepAssocInv (p : sepCarrier A.obj (sepGSet B.obj C.obj)) :
    sepCarrier (sepGSet A.obj B.obj) C.obj :=
  ⟨(⟨(p.1.1, p.1.2.1.1), sep_ab p.1.2.2 p.2⟩, p.1.2.1.2), sep_ab_c p.1.2.2 p.2⟩

/-- The reassociation bijection of the separated carriers. -/
def sepAssocEquiv (A B C : Nom) :
    sepCarrier (sepGSet A.obj B.obj) C.obj ≃ sepCarrier A.obj (sepGSet B.obj C.obj) where
  toFun := sepAssocFwd
  invFun := sepAssocInv
  left_inv _ := rfl
  right_inv _ := rfl

/-- The **associator** `(A ⊗ₙ B) ⊗ₙ C ≅ A ⊗ₙ (B ⊗ₙ C)` in `Nom`. -/
def sepAssociator (A B C : Nom) : (A ⊗ₙ B) ⊗ₙ C ≅ A ⊗ₙ (B ⊗ₙ C) :=
  ObjectProperty.isoMk _
    (Action.mkIso (Equiv.toIso (sepAssocEquiv A B C)) (by intro π; ext p; rfl))

end Associator

/-! ### The `MonoidalCategory` instance

All coherence laws reduce to identities of the underlying functions on the separated carriers
(reassociations and componentwise applications), so each is discharged by extensionality and
`rfl`. -/

open scoped MonoidalCategory in
noncomputable instance instMonoidalNom : MonoidalCategory Nom where
  tensorObj A B := sepObj A B
  whiskerLeft := fun X _ _ f => ObjectProperty.homMk (sepHom (𝟙 X.obj) f.hom)
  whiskerRight := fun f Y => ObjectProperty.homMk (sepHom f.hom (𝟙 Y.obj))
  tensorHom := fun f g => ObjectProperty.homMk (sepHom f.hom g.hom)
  tensorUnit := unitObj
  associator A B C := sepAssociator A B C
  leftUnitor A := sepLeftUnitor A
  rightUnitor A := sepRightUnitor A
  tensorHom_def := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  id_tensorHom_id := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  tensorHom_comp_tensorHom := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  whiskerLeft_id := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  id_whiskerRight := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  associator_naturality := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  leftUnitor_naturality := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  rightUnitor_naturality := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  pentagon := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  triangle := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl

/-- `Nom` is symmetric monoidal under the separated product, with the swap braiding. -/
noncomputable instance instSymmetricNom : SymmetricCategory Nom where
  braiding A B := sepBraiding A B
  braiding_naturality_right := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  braiding_naturality_left := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  hexagon_forward := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  hexagon_reverse := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl
  symmetry := by
    intros; apply ObjectProperty.hom_ext; ext p; rfl

/-! ## STEP 3 — monoidal closure `A ⊸ B`

`Nom` is monoidal closed for the separated product, and the exponential is *not* the naive
function space: it is the separated function space `A ⊸ₛ B`, the fresh-agreement quotient of the
finitely supported functions. The `MonoidalClosed Nom` instance is completed and registered as
`Nominal.monoidalClosedNom` in `CatCrypt.Category.NominalMonoidalClosedComplete` (axioms only
`propext`, `Classical.choice`, `Quot.sound`).

The internal hom starts from the nominal set of **finitely supported functions** `A.V → B.V`, where
`PermAtom` acts by conjugation `(π • f) x = B.ρ π (f (A.ρ π⁻¹ x))` and the carrier is cut down to
those `f` with `HasFinSupport` for this action. `MonoidalClosed Nom` asks for a right adjoint to
`· ⊗ₙ A`, i.e. a natural equivalence `Nom(A ⊗ₙ B, C) ≃ Nom(A, B ⊸ C)` (equivariant currying, with
the *fresh* argument condition supplying well-definedness of uncurrying on separated pairs).

The development, built on STEP 1 and STEP 2, proceeds in order:

* `funGSet A B` : the conjugation-action `GSet` on `A.V → B.V`, with `IsNominal` for its
  finite-support carrier. The support-of-a-function bound `supp f ⊆ s` when `s` supports `f` reuses
  STEP 1; nominality of the carrier is by construction (the carrier is the finite-support subtype).
* the currying and uncurrying maps, each shown equivariant, with uncurrying's well-definedness on a
  separated pair `(a, b)` using freshness of `a` for the curried function (STEP 1's `supp`);
* the two triangle/naturality identities of the adjunction, giving `Closed A` for every `A` and
  hence `MonoidalClosed Nom`.

The load-bearing prerequisite (least-support / `supp`) is provided by STEP 1; the closure itself
is assembled in `NominalSeparatedExp` (the separated exponential `⊸ₛ`) and completed in
`NominalMonoidalClosedComplete`. -/

end Nominal
