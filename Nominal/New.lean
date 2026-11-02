/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Nominal.Fresh
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Util.Notation3

/-!
# The freshness quantifier `И`

`И a, p a` states that `p a` holds for all but finitely many atoms. For a finitely supported
predicate this cofinite quantifier agrees with both an existential and a universal quantifier
over the atoms outside a support: this is the some/any property of the Gabbay-Pitts freshness
quantifier.

## Main definitions

* `New p`, written `И a, p a` - the set of atoms where `p` fails is finite
* `SupportsPred S p` - the finite set `S` supports the predicate `p`

## Main results

* `new_iff_exists`, `new_iff_forall` - for `p` supported by `S`, `И a, p a` is equivalent to
  `∃ a, a ∉ S ∧ p a` and to `∀ a, a ∉ S → p a`
* `exists_fresh_iff_forall_fresh`, `new_iff_exists_fresh`, `new_iff_forall_fresh` - the forms
  with a parameter `x` for a jointly equivariant relation `p : Atom → α → Prop`
* `new_and`, `new_not` - `И` commutes with conjunction and, on supported predicates, negation

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013,
  Section 3.2.
* Gabbay and Pitts, *A new approach to abstract syntax with variable binding*, Formal Aspects of
  Computing 13, 2002.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Nominal

/-- The supply of atoms is infinite. -/
instance : Infinite Atom :=
  Infinite.of_injective Atom.mk fun _ _ h => Atom.mk.inj h

/-- The freshness quantifier: `New p` holds when `p` fails at only finitely many atoms. -/
def New (p : Atom → Prop) : Prop :=
  {a | ¬ p a}.Finite

/-- `И a, p a` states that `p a` holds for all but finitely many atoms `a`. -/
scoped notation3 "И "(...)", "r:(scoped p => New p) => r

/-- The finite set `S` supports the predicate `p`: permutations fixing `S` pointwise preserve
and reflect `p`. -/
def SupportsPred (S : Finset Atom) (p : Atom → Prop) : Prop :=
  ∀ π : FinPerm, (∀ s ∈ S, π s = s) → ∀ a, p (π a) ↔ p a

/-- A transposition of two atoms outside `S` fixes `S` pointwise. -/
theorem swap_fixes_of_notMem {S : Finset Atom} {a b : Atom} (ha : a ∉ S) (hb : b ∉ S) :
    ∀ s ∈ S, FinPerm.swap a b s = s := fun _ hs =>
  FinPerm.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hs ha) (ne_of_mem_of_not_mem hs hb)

/-- `И` is the eventually-quantifier of the cofinite filter on atoms. -/
theorem new_iff_eventually_cofinite {p : Atom → Prop} :
    (И a, p a) ↔ ∀ᶠ a in Filter.cofinite, p a :=
  Filter.eventually_cofinite.symm

/-- `И` is monotone. -/
theorem New.mono {p q : Atom → Prop} (hp : И a, p a) (h : ∀ a, p a → q a) : И a, q a :=
  hp.subset fun a hq hpa => hq (h a hpa)

/-- `И` commutes with conjunction. -/
theorem new_and {p q : Atom → Prop} : (И a, p a ∧ q a) ↔ (И a, p a) ∧ И a, q a := by
  simp only [new_iff_eventually_cofinite, Filter.eventually_and]

section Supported

variable {S : Finset Atom} {p : Atom → Prop}

/-- For a supported predicate, one atom outside the support satisfying it gives all of them. -/
theorem SupportsPred.forall_of_exists (h : SupportsPred S p) {a : Atom} (ha : a ∉ S) (hpa : p a)
    (b : Atom) (hb : b ∉ S) : p b := by
  have := (h _ (swap_fixes_of_notMem ha hb) a).mpr hpa
  rwa [FinPerm.swap_apply_left] at this

/-- **Some/any, existential form.** -/
theorem new_iff_exists (h : SupportsPred S p) : (И a, p a) ↔ ∃ a, a ∉ S ∧ p a := by
  refine ⟨fun hp => ?_, fun ⟨a, ha, hpa⟩ => ?_⟩
  · obtain ⟨a, ha⟩ := (hp.union S.finite_toSet).exists_notMem
    simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, not_or, not_not] at ha
    exact ⟨a, ha.2, ha.1⟩
  · refine S.finite_toSet.subset fun b hb => ?_
    by_contra hbS
    exact hb (h.forall_of_exists ha hpa b hbS)

/-- **Some/any, universal form.** -/
theorem new_iff_forall (h : SupportsPred S p) : (И a, p a) ↔ ∀ a, a ∉ S → p a := by
  rw [new_iff_exists h]
  refine ⟨fun ⟨a, ha, hpa⟩ => h.forall_of_exists ha hpa, fun hall => ?_⟩
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset S
  exact ⟨a, ha, hall a ha⟩

/-- `И` commutes with negation on a supported predicate. -/
theorem new_not (h : SupportsPred S p) : (И a, ¬ p a) ↔ ¬ И a, p a := by
  have hn : SupportsPred S fun a => ¬ p a := fun π hπ a => not_congr (h π hπ a)
  rw [new_iff_exists hn, new_iff_forall h]
  push Not
  rfl

end Supported

/-! ### Forms with a parameter -/

section Parameter

variable {α : Type*} [NomSet α] {p : Atom → α → Prop}

/-- For a jointly equivariant relation, the section at `x` is supported by the support of `x`. -/
theorem supportsPred_of_equivariant (hp : ∀ (π : FinPerm) a x, p (π a) (π • x) ↔ p a x) (x : α) :
    SupportsPred (NomSet.supp x) fun a => p a x := fun π hπ a => by
  have := hp π a x
  rwa [NomSet.act_eq_of_supp_fixed x π hπ] at this

/-- `И a, p a x` for a jointly equivariant `p` is `∃ a, Fresh a x ∧ p a x`. -/
theorem new_iff_exists_fresh (hp : ∀ (π : FinPerm) a x, p (π a) (π • x) ↔ p a x) (x : α) :
    (И a, p a x) ↔ ∃ a, Fresh a x ∧ p a x :=
  new_iff_exists (supportsPred_of_equivariant hp x)

/-- `И a, p a x` for a jointly equivariant `p` is `∀ a, Fresh a x → p a x`. -/
theorem new_iff_forall_fresh (hp : ∀ (π : FinPerm) a x, p (π a) (π • x) ↔ p a x) (x : α) :
    (И a, p a x) ↔ ∀ a, Fresh a x → p a x :=
  new_iff_forall (supportsPred_of_equivariant hp x)

/-- **Some/any for fresh atoms**: a jointly equivariant relation holds at some atom fresh for
`x` exactly when it holds at every atom fresh for `x`. -/
theorem exists_fresh_iff_forall_fresh (hp : ∀ (π : FinPerm) a x, p (π a) (π • x) ↔ p a x) (x : α) :
    (∃ a, Fresh a x ∧ p a x) ↔ ∀ a, Fresh a x → p a x :=
  (new_iff_exists_fresh hp x).symm.trans (new_iff_forall_fresh hp x)

end Parameter

/-! ### Freshness for atoms and pairs -/

/-- An atom is fresh for an atom exactly when the two differ. -/
theorem fresh_atom_iff {a b : Atom} : Fresh a b ↔ a ≠ b :=
  Finset.mem_singleton.not

/-- An atom is fresh for a pair exactly when it is fresh for both components. -/
theorem fresh_prod_iff {α β : Type*} [NomSet α] [NomSet β] {c : Atom} {x : α} {y : β} :
    Fresh c (x, y) ↔ Fresh c x ∧ Fresh c y :=
  Finset.mem_union.not.trans not_or

end CatCrypt.Nominal
