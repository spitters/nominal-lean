/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Nominal.New
public import Nominal.NameAbstraction

/-!
# The freshness condition for binders

A function `f : Atom → α → β` supported by a finite set `S` lifts to `[𝔸]α → β` as soon as it
satisfies the freshness condition for binders `И a, ∀ x, Fresh a (f a x)`. Invariance of `f` under
renaming of the bound atom is derived from these two hypotheses.

The universal quantifier over `x` sits inside `И`: the atom `a` must be fresh for `f a x` also for
the values `x` in whose support `a` occurs, since those are the values where `a` is bound.

## Main definitions

* `Supports₂ S f` - the finite set `S` supports the two-argument function `f`
* `NameAbs.liftFCB` - the function `[𝔸]α → β` induced by `f`

## Main results

* `fcb_iff_exists`, `fcb_iff_forall` - some/any forms of the freshness condition
* `NameAbs.respect_of_fcb` - `f` respects `AbsRel` on atoms outside `S`
* `NameAbs.swap_of_fcb`, `NameAbs.absRel_respect_of_fcb` - the renaming law and the respect
  theorem for equivariant `f`
* `NameAbs.liftFCB_abs` - the computation rule on atoms outside `S`
* `NameAbs.liftFCB_smul`, `NameAbs.liftFCB_unique` - the lift is supported by `S` and is unique

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013,
  Chapter 4.
* Gabbay and Pitts, *A new approach to abstract syntax with variable binding*, Formal Aspects of
  Computing 13, 2002.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Nominal

variable {α β : Type*} [NomSet α] [NomSet β] {S : Finset Atom} {f : Atom → α → β}

/-- The finite set `S` supports the function `f`: permutations fixing `S` pointwise commute with
`f`, acting on both of its arguments. -/
def Supports₂ (S : Finset Atom) (f : Atom → α → β) : Prop :=
  ∀ π : FinPerm, (∀ s ∈ S, π s = s) → ∀ a x, f (π a) (π • x) = π • f a x

/-- A jointly equivariant function is supported by the empty set. -/
theorem supports₂_empty (hf : ∀ (π : FinPerm) a x, f (π a) (π • x) = π • f a x) :
    Supports₂ ∅ f := fun π _ => hf π

/-- A permutation preserves and reflects freshness. -/
theorem fresh_smul_iff (π : FinPerm) (a : Atom) (x : α) : Fresh (π a) (π • x) ↔ Fresh a x := by
  refine ⟨fun h => ?_, fresh_act_of_fresh π a x⟩
  simpa using fresh_act_of_fresh π⁻¹ (π a) (π • x) h

/-- The freshness condition, as a predicate on the bound atom, is supported by `S`. -/
theorem Supports₂.supportsPred (hf : Supports₂ S f) :
    SupportsPred S fun a => ∀ x, Fresh a (f a x) := fun π hπ a => by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · have := h (π • x)
    rwa [hf π hπ, fresh_smul_iff] at this
  · have := (fresh_smul_iff π a (f a (π⁻¹ • x))).mpr (h _)
    rwa [← hf π hπ, smul_inv_smul] at this

/-- **Some/any for the freshness condition, existential form.** -/
theorem fcb_iff_exists (hf : Supports₂ S f) :
    (И a, ∀ x, Fresh a (f a x)) ↔ ∃ a, a ∉ S ∧ ∀ x, Fresh a (f a x) :=
  new_iff_exists hf.supportsPred

/-- **Some/any for the freshness condition, universal form.** -/
theorem fcb_iff_forall (hf : Supports₂ S f) :
    (И a, ∀ x, Fresh a (f a x)) ↔ ∀ a, a ∉ S → ∀ x, Fresh a (f a x) :=
  new_iff_forall hf.supportsPred

namespace NameAbs

/-- Renaming a bound atom to another atom fresh for the value of `f` leaves the value unchanged. -/
theorem apply_swap_eq (hf : Supports₂ S f) {a c : Atom} {x : α} (ha : a ∉ S) (hc : c ∉ S)
    (haf : Fresh a (f a x)) (hcf : Fresh c (f a x)) :
    f c (FinPerm.swap a c • x) = f a x := by
  have h := hf _ (swap_fixes_of_notMem ha hc) a x
  rw [FinPerm.swap_apply_left] at h
  rw [h, Fresh.act_swap_fresh a c _ haf hcf]

/-- **Respect theorem**: a function supported by `S` that satisfies the freshness condition takes
equal values on `AbsRel`-related pairs whose bound atoms lie outside `S`. -/
theorem respect_of_fcb (hf : Supports₂ S f) (hfcb : И a, ∀ x, Fresh a (f a x))
    {a a' : Atom} {x x' : α} (ha : a ∉ S) (ha' : a' ∉ S) (hrel : AbsRel (a, x) (a', x')) :
    f a x = f a' x' := by
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (S ∪ {a, a'} ∪ NomSet.supp x ∪ NomSet.supp x' ∪ NomSet.supp (f a x) ∪ NomSet.supp (f a' x'))
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨⟨⟨⟨⟨hcS, hca, hca'⟩, hcx⟩, hcx'⟩, hcf⟩, hcf'⟩ := hc
  have hswap : FinPerm.swap a c • x = FinPerm.swap a' c • x' :=
    absRel_any_fresh hrel c (AbsRel.mk_fresh_pair c (a, x) (a', x') hca hcx hca' hcx')
  have hall := (fcb_iff_forall hf).mp hfcb
  rw [← apply_swap_eq hf ha hcS (hall a ha x) hcf, hswap,
    apply_swap_eq hf ha' hcS (hall a' ha' x') hcf']

/-- The renaming law for a jointly equivariant `f` with the freshness condition: this is the
hypothesis of `absRel_respect_of_swap`. -/
theorem swap_of_fcb (hf : ∀ (π : FinPerm) a x, f (π a) (π • x) = π • f a x)
    (hfcb : И a, ∀ x, Fresh a (f a x)) (a c : Atom) (x : α) (hcx : Fresh c x) (hca : c ≠ a) :
    f a x = f c (FinPerm.swap a c • x) := by
  have hsupp : Fresh c (f a x) := fun h => fresh_prod_iff.mpr ⟨fresh_atom_iff.mpr hca, hcx⟩
    (supp_sub_of_equivariant (fun p : Atom × α => f p.1 p.2) (fun π p => hf π p.1 p.2) (a, x) h)
  have hS := supports₂_empty hf
  exact (apply_swap_eq hS (Finset.notMem_empty a) (Finset.notMem_empty c)
    ((fcb_iff_forall hS).mp hfcb a (Finset.notMem_empty a) x) hsupp).symm

/-- **Respect theorem for equivariant functions.** -/
theorem absRel_respect_of_fcb (hf : ∀ (π : FinPerm) a x, f (π a) (π • x) = π • f a x)
    (hfcb : И a, ∀ x, Fresh a (f a x)) :
    ∀ a a' x x', AbsRel (a, x) (a', x') → f a x = f a' x' :=
  absRel_respect_of_swap f (swap_of_fcb hf hfcb)

/-- An atom outside `S` that is fresh for `x` and distinct from `a`. -/
theorem exists_avoid (S : Finset Atom) (a : Atom) (x : α) :
    ∃ c, c ∉ S ∧ c ≠ a ∧ Fresh c x := by
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (S ∪ {a} ∪ NomSet.supp x)
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1.1, hc.1.2, hc.2⟩

/-- A chosen atom outside `S` to which the bound atom `a` of `abs a x` can be renamed. -/
noncomputable def avoid (S : Finset Atom) (a : Atom) (x : α) : Atom :=
  (exists_avoid S a x).choose

/-- The renamed pair at `avoid S a x` is `AbsRel`-related to `(a, x)`. -/
theorem absRel_avoid (S : Finset Atom) (a : Atom) (x : α) :
    AbsRel (a, x) (avoid S a x, FinPerm.swap a (avoid S a x) • x) :=
  Quotient.exact (s := absRelSetoid α) (abs_rename a x _
    (exists_avoid S a x).choose_spec.2.2 (exists_avoid S a x).choose_spec.2.1)

/-- The bound atom outside `S` chosen by `avoid`. -/
theorem avoid_notMem (S : Finset Atom) (a : Atom) (x : α) : avoid S a x ∉ S :=
  (exists_avoid S a x).choose_spec.1

/-- **The FCB recursor**: the function on `[𝔸]α` induced by a function `f` supported by `S` that
satisfies the freshness condition. It evaluates `f` on a representative whose bound atom lies
outside `S`. -/
noncomputable def liftFCB (S : Finset Atom) (f : Atom → α → β) (hf : Supports₂ S f)
    (hfcb : И a, ∀ x, Fresh a (f a x)) : NameAbs α → β :=
  NameAbs.lift (fun a x => f (avoid S a x) (FinPerm.swap a (avoid S a x) • x))
    fun a a' x x' hrel => respect_of_fcb hf hfcb (avoid_notMem S a x) (avoid_notMem S a' x')
      ((AbsRel.symm (absRel_avoid S a x)).trans (hrel.trans (absRel_avoid S a' x')))

/-- **Computation rule** of the FCB recursor on atoms outside `S`. -/
theorem liftFCB_abs (hf : Supports₂ S f) (hfcb : И a, ∀ x, Fresh a (f a x)) {a : Atom}
    (ha : a ∉ S) (x : α) : liftFCB S f hf hfcb (abs a x) = f a x :=
  respect_of_fcb hf hfcb (avoid_notMem S a x) ha (absRel_avoid S a x).symm

/-- Every abstraction has a representative whose bound atom lies outside `S`. -/
theorem exists_abs_notMem (S : Finset Atom) (q : NameAbs α) :
    ∃ a x, a ∉ S ∧ q = abs a x := by
  obtain ⟨⟨a, x⟩, rfl⟩ := q.exists_rep
  exact ⟨avoid S a x, _, avoid_notMem S a x, Quotient.sound (absRel_avoid S a x)⟩

/-- The FCB recursor is supported by `S`: permutations fixing `S` pointwise commute with it. -/
theorem liftFCB_smul (hf : Supports₂ S f) (hfcb : И a, ∀ x, Fresh a (f a x)) (π : FinPerm)
    (hπ : ∀ s ∈ S, π s = s) (q : NameAbs α) :
    liftFCB S f hf hfcb (π • q) = π • liftFCB S f hf hfcb q := by
  obtain ⟨a, x, ha, rfl⟩ := exists_abs_notMem S q
  have hπa : π a ∉ S := fun h => ha (by
    have := hπ _ h
    rwa [π.val.injective this] at h)
  rw [smul_abs, liftFCB_abs hf hfcb ha]
  exact (liftFCB_abs hf hfcb hπa _).trans (hf π hπ a x)

/-- **Uniqueness**: the FCB recursor is the only function on `[𝔸]α` satisfying the computation
rule on atoms outside `S`. -/
theorem liftFCB_unique (hf : Supports₂ S f) (hfcb : И a, ∀ x, Fresh a (f a x))
    (g : NameAbs α → β) (hg : ∀ a x, a ∉ S → g (abs a x) = f a x) :
    g = liftFCB S f hf hfcb := by
  funext q
  obtain ⟨a, x, ha, rfl⟩ := exists_abs_notMem S q
  rw [hg a x ha, liftFCB_abs hf hfcb ha]

end NameAbs

end CatCrypt.Nominal
