/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.NominalCoreEquivalence
import Nominal.NameAbstraction

set_option autoImplicit false

/-!
# Categorical recursion for `[𝔸](−)`, and the SSProve identification of name abstraction

This file lands the atom-abstraction development on SSProve's *own* core name abstraction. It has
two parts.

## Part 1 — the categorical recursion principle `absRec`

`absRec` is the eliminator *out of* the categorical abstraction `[𝔸]X` on `Nom`: given a target
`Y : Nom` and an atom-indexed `g : Atom → X.V → Y.V` that is equivariant (`hg`) and respects the
categorical α-equivalence `AbsRel X` (`hcompat`), it produces a `Nom`-morphism
`absRec g hg hcompat : [𝔸]X ⟶ Y` with the computation/β-rule `absRec … (absPt X a x) = g a x`
(`absRec_absPt`). This is `Quotient.lift` promoted to an equivariant `Action.Hom`, mirroring the
core `NameAbs.lift`.

`absRel_respect_of_swap` is the freshness-condition-for-binders (FCB) upgrade, mirroring the core
`NameAbs.absRel_respect_of_swap`: it derives the `AbsRel`-respect hypothesis from the single
renaming law `g a x = g c (swap a c • x)` for `c` fresh. `absRecOfSwap` packages the eliminator
built through it.

## Part 2 — the SSProve identification `coreAbsIso`

`coreAbsIso β : coreToNom (NameAbs β) ≅ absObj (coreToNom β)` transports SSProve's own name
abstraction `NameAbs β` (its core `[𝔸]β` over `FinPerm`, `CatCryptCore.Nominal.NameAbstraction`)
into the categorical world and identifies it with the *native* categorical abstraction `absObj` of
the transported `β`. Both are quotients of `Atom × β` by α-equivalence; the identification is the
carrier bijection `abs a x ↦ absPt (coreAtomEquiv a) x`, proved well defined (both directions),
bijective, and equivariant — an isomorphism of `Nom` objects. The transported `coreToNom` is the
*canonical* one from `NominalCoreEquivalence` (the object tied to the proven Schanuel equivalence
`nomFinEquivNom`), so the iso identifies SSProve's actual binder object.

This is delivered at the **object level** (a `Nom`-iso for each `β`), the required SSProve payoff.
Packaging the object isos into a natural isomorphism of the two functors `NomSet ⥤ Nom` is not
carried out (it needs naturality of the transport in `β`); it is the single residual.

### The `FinPerm`-vs-`Perm` compatibility

The two α-equivalences swap by different transpositions: the core `AbsRel` uses
`CatCrypt.Nominal.FinPerm.swap` (a `FinPerm`), the categorical `AbsRel` uses `Equiv.swap` over the
full permutation group. `swap_transport` reconciles them: the reconstructed full-`Perm` action of
`coreToNom β` on `Equiv.swap (coreAtomEquiv a) (coreAtomEquiv c)` is exactly the core
`FinPerm.swap a c` action. Its proof factors through `fromPermℕ_swap` (the transposition transports
along the atom equivalence) and `fullSmul_val` (the reconstructed action agrees with the native
`FinPerm`-action on a genuine `FinPerm`).

## A note on the local abstraction machinery

The categorical abstraction `absObj`/`absPt`/`AbsRel` and its support-shrink lemmas are re-derived
here (Section 0, elementary and definitionally the constructions of
`CatCrypt.Category.NominalAbstraction`) rather than imported. This is forced: `NominalAbstraction`
and `NominalCoreBridge` (whose `coreToNom` Part 2 needs, canonically) both declare
`Nominal.act_eq_of_agree`, so the two modules cannot be co-imported. Keeping the canonical
`coreToNom` (the SSProve link) and re-deriving the elementary abstraction side under the local name
`act_eq_of_agree_gset` is the resolution that touches no existing file.

Everything below is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

namespace Nominal

open CatCrypt.Nominal (NomSet FinPerm Fresh abs NameAbs smul_abs absRel_any_fresh
  act_eq_of_agree_on_supp)

/-! ## Section 0 — the atom abstraction `[𝔸](−)` on `Nom` (elementary re-derivation)

Verbatim constructions of `CatCrypt.Category.NominalAbstraction`, re-proved here because that
module cannot be co-imported with `NominalCoreBridge` (both declare `Nominal.act_eq_of_agree`; the
support lemma is renamed `act_eq_of_agree_gset` here). -/

/-- If two permutations `g` and `h` agree on a support `s` of `x`, they act equally on `x`. -/
lemma act_eq_of_agree_gset {X : GSet} {s : Finset Atom} {x : X.V}
    (hs : Supports X s x) {g h : PermAtom} (hgh : ∀ a ∈ s, g a = h a) :
    X.ρ g x = X.ρ h x := by
  have key : ∀ a ∈ s, (h⁻¹ * g) a = a := by
    intro a ha
    rw [Equiv.Perm.mul_apply, hgh a ha]; simp
  have hx : X.ρ (h⁻¹ * g) x = x := hs _ key
  calc X.ρ g x = X.ρ (h * (h⁻¹ * g)) x := by rw [mul_inv_cancel_left]
    _ = X.ρ h (X.ρ (h⁻¹ * g) x) := GSet.act_mul X h (h⁻¹ * g) x
    _ = X.ρ h x := by rw [hx]

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

/-- α-equivalence on representatives `Atom × X.V`, cofinite form. -/
def AbsRel (X : GSet) (p q : Atom × X.V) : Prop :=
  ∃ s : Finset Atom, ∀ c ∉ s, X.ρ (Equiv.swap p.1 c) p.2 = X.ρ (Equiv.swap q.1 c) q.2

namespace AbsRel

variable {X : GSet}

theorem refl (p : Atom × X.V) : AbsRel X p p := ⟨∅, fun _ _ => rfl⟩

theorem symm {p q : Atom × X.V} (h : AbsRel X p q) : AbsRel X q p := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun c hc => (hs c hc).symm⟩

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
    AbsRel X (π p.1, X.ρ π p.2) (π q.1, X.ρ π q.2) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s.image π, fun d hd => ?_⟩
  have hc : π⁻¹ d ∉ s := by
    intro hmem
    exact hd (by
      have : π (π⁻¹ d) = d := by simp
      simpa [this] using Finset.mem_image_of_mem π hmem)
  have hkey := hs (π⁻¹ d) hc
  have hdc : π (π⁻¹ d) = d := by simp
  calc X.ρ (Equiv.swap (π p.1) d) (X.ρ π p.2)
      = X.ρ (Equiv.swap (π p.1) (π (π⁻¹ d)) * π) p.2 := by
        rw [hdc, ← GSet.act_mul]
    _ = X.ρ (π * Equiv.swap p.1 (π⁻¹ d)) p.2 := by rw [swap_mul_perm]
    _ = X.ρ π (X.ρ (Equiv.swap p.1 (π⁻¹ d)) p.2) := GSet.act_mul X _ _ _
    _ = X.ρ π (X.ρ (Equiv.swap q.1 (π⁻¹ d)) q.2) := by rw [hkey]
    _ = X.ρ (π * Equiv.swap q.1 (π⁻¹ d)) q.2 := (GSet.act_mul X _ _ _).symm
    _ = X.ρ (Equiv.swap (π q.1) (π (π⁻¹ d)) * π) q.2 := by rw [swap_mul_perm]
    _ = X.ρ (Equiv.swap (π q.1) d) (X.ρ π q.2) := by rw [hdc, ← GSet.act_mul]

/-- The underlying `GSet` of `[𝔸]X`. -/
def absGSet (X : GSet) : GSet where
  V := Quotient (absSetoid X)
  ρ :=
    { toFun := fun π => Quotient.map (fun p => (π p.1, X.ρ π p.2)) (fun _ _ h => AbsRel_smul π h)
      map_one' := by
        funext q
        induction q using Quotient.inductionOn with
        | _ p =>
          show Quotient.mk (absSetoid X) ((1 : PermAtom) p.1, X.ρ (1 : PermAtom) p.2)
            = Quotient.mk (absSetoid X) p
          rw [Equiv.Perm.one_apply, GSet.act_one]
      map_mul' := fun a b => by
        funext q
        induction q using Quotient.inductionOn with
        | _ p =>
          show Quotient.mk (absSetoid X) ((a * b) p.1, X.ρ (a * b) p.2)
            = Quotient.mk (absSetoid X) (a (b p.1), X.ρ a (X.ρ b p.2))
          rw [GSet.act_mul]; rfl }

/-- Abstraction point: the class of `(a, x)` in `[𝔸]X`. -/
def absPt (X : GSet) (a : Atom) (x : X.V) : (absGSet X).V :=
  Quotient.mk (absSetoid X) (a, x)

@[simp] lemma absGSet_ρ_mk (X : GSet) (π : PermAtom) (a : Atom) (x : X.V) :
    (absGSet X).ρ π (absPt X a x) = absPt X (π a) (X.ρ π x) := rfl

/-- **Support-shrink**: if `s` supports `x`, then `s \ {a}` supports the class of `(a, x)`. -/
theorem absGSet_supports {X : GSet} {s : Finset Atom} {a : Atom} {x : X.V}
    (hs : Supports X s x) : Supports (absGSet X) (s \ {a}) (absPt X a x) := by
  intro π hπ
  show Quotient.mk (absSetoid X) (π a, X.ρ π x) = Quotient.mk (absSetoid X) (a, x)
  apply Quotient.sound
  refine ⟨insert a (insert (π a) s), fun c hc => ?_⟩
  simp only [Finset.mem_insert, not_or] at hc
  obtain ⟨hca, hcπa, hcs⟩ := hc
  show X.ρ (Equiv.swap (π a) c) (X.ρ π x) = X.ρ (Equiv.swap a c) x
  rw [← GSet.act_mul]
  apply act_eq_of_agree_gset hs
  intro d hd
  rw [Equiv.Perm.mul_apply]
  by_cases hda : d = a
  · subst hda
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · have hπd : π d = d := hπ d (Finset.mem_sdiff.mpr ⟨hd, Finset.notMem_singleton.mpr hda⟩)
    have hdc : d ≠ c := fun h => hcs (h ▸ hd)
    have hdπa : d ≠ π a := by
      intro h
      exact hda (π.injective (by rw [hπd, h]))
    rw [hπd, Equiv.swap_apply_of_ne_of_ne hdπa hdc, Equiv.swap_apply_of_ne_of_ne hda hdc]

/-- `[𝔸]X` is a nominal set. -/
theorem absGSet_isNominal {X : GSet} (hX : IsNominal X) : IsNominal (absGSet X) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    obtain ⟨s, hs⟩ := hX p.2
    exact ⟨s \ {p.1}, absGSet_supports hs⟩

/-- Atom abstraction `[𝔸]X` on objects of `Nom`. -/
def absObj (X : Nom) : Nom := Nom.of (absGSet X.obj) (absGSet_isNominal X.property)

@[inherit_doc] notation "[𝔸]" X => absObj X

/-- Equivariance/renaming law: if `b` is fresh for `x` and `b ≠ a`, then abstracting at `a`
equals abstracting at `b` after swapping. -/
theorem absPt_rename {X : GSet} {s : Finset Atom} {a b : Atom} {x : X.V}
    (hs : Supports X s x) (hb : b ∉ s) (hba : b ≠ a) :
    absPt X a x = absPt X b (X.ρ (Equiv.swap a b) x) := by
  apply Quotient.sound
  refine ⟨insert a (insert b s), fun c hc => ?_⟩
  simp only [Finset.mem_insert, not_or] at hc
  obtain ⟨hca, hcb, hcs⟩ := hc
  show X.ρ (Equiv.swap a c) x = X.ρ (Equiv.swap b c) (X.ρ (Equiv.swap a b) x)
  rw [← GSet.act_mul]
  apply act_eq_of_agree_gset hs
  intro d hd
  have hdc : d ≠ c := fun h => hcs (h ▸ hd)
  have hdb : d ≠ b := fun h => hb (h ▸ hd)
  rw [Equiv.Perm.mul_apply]
  by_cases hda : d = a
  · subst hda
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne hda hdc, Equiv.swap_apply_of_ne_of_ne hda hdb,
        Equiv.swap_apply_of_ne_of_ne hdb hdc]

/-! ## Part 1 — categorical recursion for `[𝔸](−)` -/

/-- The underlying `GSet` morphism of the categorical abstraction eliminator: `Quotient.lift` of an
equivariant, `AbsRel`-respecting atom-indexed function. -/
def absRecHom {X : Nom} {Y : Nom} (g : Atom → X.obj.V → Y.obj.V)
    (hg : ∀ (π : PermAtom) (a : Atom) (x : X.obj.V),
      g (π a) (X.obj.ρ π x) = Y.obj.ρ π (g a x))
    (hcompat : ∀ a a' x x', AbsRel X.obj (a, x) (a', x') → g a x = g a' x') :
    absGSet X.obj ⟶ Y.obj where
  hom := Quotient.lift (fun p => g p.1 p.2) (fun p q h => hcompat p.1 q.1 p.2 q.2 h)
  comm := by
    intro π
    funext q
    induction q using Quotient.inductionOn with
    | _ p => exact hg π p.1 p.2

/-- **Categorical recursion principle** for atom abstraction on `Nom`. Given a target `Y` and an
equivariant `g : Atom → X.V → Y.V` respecting the α-equivalence `AbsRel X`, produce the
`Nom`-morphism `[𝔸]X ⟶ Y`. The `Quotient.lift`-based eliminator, mirroring `NameAbs.lift`. -/
def absRec {X : Nom} {Y : Nom} (g : Atom → X.obj.V → Y.obj.V)
    (hg : ∀ (π : PermAtom) (a : Atom) (x : X.obj.V),
      g (π a) (X.obj.ρ π x) = Y.obj.ρ π (g a x))
    (hcompat : ∀ a a' x x', AbsRel X.obj (a, x) (a', x') → g a x = g a' x') :
    absObj X ⟶ Y :=
  ObjectProperty.homMk (absRecHom g hg hcompat)

/-- **Computation rule** (β-rule) for the categorical eliminator:
`absRec g hg hcompat (absPt X a x) = g a x`. -/
@[simp] theorem absRec_absPt {X : Nom} {Y : Nom} (g : Atom → X.obj.V → Y.obj.V)
    (hg : ∀ (π : PermAtom) (a : Atom) (x : X.obj.V),
      g (π a) (X.obj.ρ π x) = Y.obj.ρ π (g a x))
    (hcompat : ∀ a a' x x', AbsRel X.obj (a, x) (a', x') → g a x = g a' x')
    (a : Atom) (x : X.obj.V) :
    (absRec g hg hcompat).hom.hom (absPt X.obj a x) = g a x := rfl

/-- **FCB upgrade** (freshness condition for binders), mirroring `NameAbs.absRel_respect_of_swap`:
from the renaming law `g a x = g c (swap a c • x)` for `c` fresh for `x` (outside a support `s`),
the atom-indexed `g` respects the categorical α-equivalence `AbsRel X`. -/
theorem absRel_respect_of_swap {X : Nom} {Y : Type*} (g : Atom → X.obj.V → Y)
    (hswap : ∀ (a c : Atom) (x : X.obj.V) (s : Finset Atom),
      Supports X.obj s x → c ∉ s → c ≠ a → g a x = g c (X.obj.ρ (Equiv.swap a c) x)) :
    ∀ a a' x x', AbsRel X.obj (a, x) (a', x') → g a x = g a' x' := by
  intro a a' x x' hrel
  obtain ⟨w, hw⟩ := hrel
  obtain ⟨sx, hsx⟩ := X.property x
  obtain ⟨sx', hsx'⟩ := X.property x'
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (w ∪ sx ∪ sx' ∪ {a, a'})
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨⟨⟨hcw, hcsx⟩, hcsx'⟩, hca, hca'⟩ := hc
  have heq : X.obj.ρ (Equiv.swap a c) x = X.obj.ρ (Equiv.swap a' c) x' := hw c hcw
  rw [hswap a c x sx hsx hcsx hca, hswap a' c x' sx' hsx' hcsx' hca', heq]

/-- The eliminator built through the FCB (`absRel_respect_of_swap`). -/
def absRecOfSwap {X : Nom} {Y : Nom} (g : Atom → X.obj.V → Y.obj.V)
    (hg : ∀ (π : PermAtom) (a : Atom) (x : X.obj.V),
      g (π a) (X.obj.ρ π x) = Y.obj.ρ π (g a x))
    (hswap : ∀ (a c : Atom) (x : X.obj.V) (s : Finset Atom),
      Supports X.obj s x → c ∉ s → c ≠ a → g a x = g c (X.obj.ρ (Equiv.swap a c) x)) :
    absObj X ⟶ Y :=
  absRec g hg (absRel_respect_of_swap g hswap)

/-! ## Part 2 — the SSProve identification

Throughout, `β` is a core nominal set; `coreToNom β` is its canonical categorical presentation. -/

variable {β : Type} [NomSet β]

/-! ### `FinPerm`-vs-`Perm` compatibility -/

/-- The reconstructed full-`Perm` action of `coreToNom β` on a genuine `FinPerm` (given as its
underlying permutation) agrees with the native core `FinPerm`-action. -/
lemma fullSmul_val (τ : FinPerm) (x : β) : fullSmul τ.val x = τ • x := by
  show extendPerm τ.val (NomSet.supp x) • x = τ • x
  apply act_eq_of_agree_on_supp
  intro b hb
  rw [extendPerm_spec τ.val (NomSet.supp x) b hb]
  rfl

/-- The transposition transports along the atom equivalence. -/
lemma fromPermℕ_swap (a c : CatCrypt.Nominal.Atom) :
    fromPermℕ (Equiv.swap (coreAtomEquiv a) (coreAtomEquiv c)) = (FinPerm.swap a c).val := by
  have h : finPermToPerm (FinPerm.swap a c)
      = Equiv.swap (coreAtomEquiv a) (coreAtomEquiv c) := by
    simp only [finPermToPerm, MonoidHom.coe_mk, OneHom.coe_mk, CatCrypt.Nominal.FinPerm.swap_val]
    exact Equiv.symm_trans_swap_trans a c coreAtomEquiv
  rw [← h, fromPermℕ_finPermToPerm]

/-- **The compatibility lemma.** The reconstructed full-`Perm` action of `coreToNom β` on the
categorical transposition is exactly the core `FinPerm.swap a c` action. -/
lemma swap_transport (a c : CatCrypt.Nominal.Atom) (x : β) :
    (coreToNom β).obj.ρ (Equiv.swap (coreAtomEquiv a) (coreAtomEquiv c)) x
      = FinPerm.swap a c • x := by
  show fullSmul (fromPermℕ (Equiv.swap (coreAtomEquiv a) (coreAtomEquiv c))) x
      = FinPerm.swap a c • x
  rw [fromPermℕ_swap]
  exact fullSmul_val (FinPerm.swap a c) x

/-- The reconstructed action of `coreToNom β` on a transported `FinPerm` is the native action. -/
lemma coreToNom_finPerm_act (τ : FinPerm) (x : β) :
    (coreToNom β).obj.ρ (finPermToPerm τ) x = τ • x := by
  show fullSmul (fromPermℕ (finPermToPerm τ)) x = τ • x
  rw [fromPermℕ_finPermToPerm]
  exact fullSmul_val τ x

/-! ### Well-definedness of the carrier bijection -/

/-- Core α-equivalence transports to categorical α-equivalence. -/
lemma absRel_core_to_cat {p q : CatCrypt.Nominal.Atom × β}
    (h : CatCrypt.Nominal.AbsRel p q) :
    AbsRel (coreToNom β).obj (coreAtomEquiv p.1, p.2) (coreAtomEquiv q.1, q.2) := by
  obtain ⟨a, x⟩ := p
  obtain ⟨a', x'⟩ := q
  refine ⟨(NomSet.supp x ∪ NomSet.supp x' ∪ {a, a'}).image coreAtomEquiv, ?_⟩
  intro d hd
  set d0 := coreAtomEquiv.symm d with hd0
  have hdd0 : coreAtomEquiv d0 = d := coreAtomEquiv.apply_symm_apply d
  have hns : d0 ∉ (NomSet.supp x ∪ NomSet.supp x' ∪ {a, a'}) := by
    intro hmem
    exact hd (by rw [← hdd0]; exact Finset.mem_image_of_mem _ hmem)
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hns
  obtain ⟨⟨hx, hx'⟩, ha, ha'⟩ := hns
  show (coreToNom β).obj.ρ (Equiv.swap (coreAtomEquiv a) d) x
      = (coreToNom β).obj.ρ (Equiv.swap (coreAtomEquiv a') d) x'
  rw [← hdd0, swap_transport, swap_transport]
  have hfresh : Fresh d0 ((a, x), (a', x')) :=
    CatCrypt.Nominal.AbsRel.mk_fresh_pair d0 (a, x) (a', x') ha hx ha' hx'
  exact absRel_any_fresh h d0 hfresh

/-- Categorical α-equivalence transports back to core α-equivalence. -/
lemma absRel_cat_to_core {p q : Atom × β}
    (h : AbsRel (coreToNom β).obj p q) :
    CatCrypt.Nominal.AbsRel (coreAtomEquiv.symm p.1, p.2) (coreAtomEquiv.symm q.1, q.2) := by
  obtain ⟨n, x⟩ := p
  obtain ⟨n', x'⟩ := q
  obtain ⟨s, hs⟩ := h
  set S := NomSet.supp x ∪ NomSet.supp x' ∪ {coreAtomEquiv.symm n, coreAtomEquiv.symm n'}
      ∪ s.image coreAtomEquiv.symm with hSdef
  set c := CatCrypt.Nominal.Atom.fresh S with hcdef
  have hc : c ∉ S := CatCrypt.Nominal.Atom.fresh_not_mem S
  rw [hSdef] at hc
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨⟨⟨hx, hx'⟩, hn, hn'⟩, himg⟩ := hc
  have hcs : coreAtomEquiv c ∉ s := by
    intro hmem
    apply himg
    have hmem2 : coreAtomEquiv.symm (coreAtomEquiv c) ∈ s.image coreAtomEquiv.symm :=
      Finset.mem_image_of_mem _ hmem
    rwa [coreAtomEquiv.symm_apply_apply] at hmem2
  have hswap := hs (coreAtomEquiv c) hcs
  rw [show n = coreAtomEquiv (coreAtomEquiv.symm n) from (coreAtomEquiv.apply_symm_apply n).symm,
      show n' = coreAtomEquiv (coreAtomEquiv.symm n') from (coreAtomEquiv.apply_symm_apply n').symm,
      swap_transport, swap_transport] at hswap
  refine ⟨c, ?_, hswap⟩
  exact CatCrypt.Nominal.AbsRel.mk_fresh_pair c
    (coreAtomEquiv.symm n, x) (coreAtomEquiv.symm n', x') hn hx hn' hx'

/-! ### The carrier bijection -/

/-- Forward map: `abs a x ↦ absPt (coreAtomEquiv a) x`. -/
noncomputable def coreAbsFwd (β : Type) [NomSet β] :
    NameAbs β → (absObj (coreToNom β)).obj.V :=
  Quotient.lift (fun p => absPt (coreToNom β).obj (coreAtomEquiv p.1) p.2)
    (fun _ _ h => Quotient.sound (absRel_core_to_cat h))

/-- Backward map: `absPt n x ↦ abs (coreAtomEquiv.symm n) x`. -/
noncomputable def coreAbsBwd (β : Type) [NomSet β] :
    (absObj (coreToNom β)).obj.V → NameAbs β :=
  Quotient.lift (fun p => abs (coreAtomEquiv.symm p.1) p.2)
    (fun _ _ h => Quotient.sound (absRel_cat_to_core h))

/-- The carrier bijection `NameAbs β ≃ (absObj (coreToNom β)).V`. -/
noncomputable def coreAbsEquiv (β : Type) [NomSet β] :
    NameAbs β ≃ (absObj (coreToNom β)).obj.V where
  toFun := coreAbsFwd β
  invFun := coreAbsBwd β
  left_inv := by
    intro w
    induction w using Quotient.inductionOn with
    | _ p =>
      obtain ⟨a, x⟩ := p
      show abs (coreAtomEquiv.symm (coreAtomEquiv a)) x = abs a x
      rw [Equiv.symm_apply_apply]
  right_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | _ p =>
      obtain ⟨n, x⟩ := p
      show absPt (coreToNom β).obj (coreAtomEquiv (coreAtomEquiv.symm n)) x
          = absPt (coreToNom β).obj n x
      rw [Equiv.apply_symm_apply]

/-! ### Equivariance -/

/-- Equivariance of the forward map against the native `FinPerm`-action on the domain and the
transported action on the codomain. -/
lemma coreAbs_finPerm (τ : FinPerm) (w : NameAbs β) :
    coreAbsFwd β (τ • w)
      = (absObj (coreToNom β)).obj.ρ (finPermToPerm τ) (coreAbsFwd β w) := by
  induction w using Quotient.inductionOn with
  | _ p =>
    obtain ⟨a, x⟩ := p
    show coreAbsFwd β (τ • abs a x)
        = (absGSet (coreToNom β).obj).ρ (finPermToPerm τ) (coreAbsFwd β (abs a x))
    rw [smul_abs]
    show absPt (coreToNom β).obj (coreAtomEquiv (τ • a)) (τ • x)
        = (absGSet (coreToNom β).obj).ρ (finPermToPerm τ)
            (absPt (coreToNom β).obj (coreAtomEquiv a) x)
    rw [absGSet_ρ_mk]
    have h1 : coreAtomEquiv (τ • a) = finPermToPerm τ (coreAtomEquiv a) := by
      have hsa : (τ • a) = τ.val a := rfl
      rw [hsa]
      simp only [finPermToPerm, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.permCongr_apply,
        Equiv.symm_apply_apply]
    have h2 : (τ • x : β) = (coreToNom β).obj.ρ (finPermToPerm τ) x :=
      (coreToNom_finPerm_act τ x).symm
    rw [h1, h2]

/-- **Equivariance** of the forward map against the reconstructed full-`Perm` actions on both
sides. Reduces the full permutation to a `FinPerm` agreeing on the relevant supports, then applies
`coreAbs_finPerm`. -/
lemma coreAbs_equiv (π : PermAtom) (w : NameAbs β) :
    coreAbsFwd β ((coreToNom (NameAbs β)).obj.ρ π w)
      = (absObj (coreToNom β)).obj.ρ π (coreAbsFwd β w) := by
  obtain ⟨sx, hsx⟩ := (coreToNom (NameAbs β)).property w
  obtain ⟨sy, hsy⟩ := (absObj (coreToNom β)).property (coreAbsFwd β w)
  obtain ⟨τ, hτ⟩ := finPermToPerm_agree_on_finset π (sx ∪ sy)
  have hx : (coreToNom (NameAbs β)).obj.ρ π w
      = (coreToNom (NameAbs β)).obj.ρ (finPermToPerm τ) w :=
    act_eq_of_supports hsx (fun a ha => (hτ a (Finset.mem_union_left sy ha)).symm)
  have hy : (absObj (coreToNom β)).obj.ρ (finPermToPerm τ) (coreAbsFwd β w)
      = (absObj (coreToNom β)).obj.ρ π (coreAbsFwd β w) :=
    act_eq_of_supports hsy (fun a ha => hτ a (Finset.mem_union_right sx ha))
  rw [hx, ← hy, coreToNom_finPerm_act, coreAbs_finPerm]

/-! ### The isomorphism -/

/-- The underlying `GSet` isomorphism `coreToNom (NameAbs β) ≅ absObj (coreToNom β)`. -/
noncomputable def coreAbsGSetIso (β : Type) [NomSet β] :
    (coreToNom (NameAbs β)).obj ≅ (absObj (coreToNom β)).obj :=
  Action.mkIso (Equiv.toIso (coreAbsEquiv β))
    (by
      intro π
      funext w
      exact coreAbs_equiv π w)

/-- The forward map computes as `abs a x ↦ absPt (coreAtomEquiv a) x`. -/
@[simp] lemma coreAbsGSetIso_hom_apply (β : Type) [NomSet β]
    (a : CatCrypt.Nominal.Atom) (x : β) :
    (coreAbsGSetIso β).hom.hom (abs a x) = absPt (coreToNom β).obj (coreAtomEquiv a) x := rfl

/-- **The SSProve identification.** SSProve's own name abstraction `NameAbs β` (its core `[𝔸]β`
over `FinPerm`), transported into the categorical world via the canonical `coreToNom`, is the
native categorical abstraction `[𝔸]` of the transported `β`. An isomorphism of `Nom` objects. -/
noncomputable def coreAbsIso (β : Type) [NomSet β] :
    coreToNom (NameAbs β) ≅ absObj (coreToNom β) :=
  ObjectProperty.isoMk _ (coreAbsGSetIso β)

end Nominal
