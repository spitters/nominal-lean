/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.NominalCoreEquivalence
import Nominal.Category.NominalAbstraction
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

## The abstraction machinery

The categorical abstraction `absObj`/`absPt`/`AbsRel` and its support-shrink lemmas come from
`CatCrypt.Category.NominalAbstraction`, imported alongside the canonical `coreToNom` from
`NominalCoreEquivalence`/`NominalCoreBridge` (which Part 2 needs).

Everything below is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

namespace Nominal

open CatCrypt.Nominal (NomSet FinPerm Fresh abs NameAbs smul_abs absRel_any_fresh
  act_eq_of_agree_on_supp)

/-! ## Part 1 — categorical recursion for `[𝔸](−)` -/

/-- The underlying `GSet` morphism of the categorical abstraction eliminator: `Quotient.lift` of an
equivariant, `AbsRel`-respecting atom-indexed function. -/
def absRecHom {X : Nom} {Y : Nom} (g : Atom → X.obj.V → Y.obj.V)
    (hg : ∀ (π : PermAtom) (a : Atom) (x : X.obj.V),
      g (π a) (X.obj.act π x) = Y.obj.act π (g a x))
    (hcompat : ∀ a a' x x', AbsRel X.obj (a, x) (a', x') → g a x = g a' x') :
    absGSet X.obj ⟶ Y.obj where
  hom := TypeCat.ofHom (Quotient.lift (fun p => g p.1 p.2) (fun p q h => hcompat p.1 q.1 p.2 q.2 h))
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro q
    induction q using Quotient.inductionOn with
    | _ p => exact hg π p.1 p.2

/-- **Categorical recursion principle** for atom abstraction on `Nom`. Given a target `Y` and an
equivariant `g : Atom → X.V → Y.V` respecting the α-equivalence `AbsRel X`, produce the
`Nom`-morphism `[𝔸]X ⟶ Y`. The `Quotient.lift`-based eliminator, mirroring `NameAbs.lift`. -/
def absRec {X : Nom} {Y : Nom} (g : Atom → X.obj.V → Y.obj.V)
    (hg : ∀ (π : PermAtom) (a : Atom) (x : X.obj.V),
      g (π a) (X.obj.act π x) = Y.obj.act π (g a x))
    (hcompat : ∀ a a' x x', AbsRel X.obj (a, x) (a', x') → g a x = g a' x') :
    absObj X ⟶ Y :=
  ObjectProperty.homMk (absRecHom g hg hcompat)

/-- **Computation rule** (β-rule) for the categorical eliminator:
`absRec g hg hcompat (absPt X a x) = g a x`. -/
@[simp] theorem absRec_absPt {X : Nom} {Y : Nom} (g : Atom → X.obj.V → Y.obj.V)
    (hg : ∀ (π : PermAtom) (a : Atom) (x : X.obj.V),
      g (π a) (X.obj.act π x) = Y.obj.act π (g a x))
    (hcompat : ∀ a a' x x', AbsRel X.obj (a, x) (a', x') → g a x = g a' x')
    (a : Atom) (x : X.obj.V) :
    (absRec g hg hcompat).hom.hom (absPt X.obj a x) = g a x := rfl

/-- **FCB upgrade** (freshness condition for binders), mirroring `NameAbs.absRel_respect_of_swap`:
from the renaming law `g a x = g c (swap a c • x)` for `c` fresh for `x` (outside a support `s`),
the atom-indexed `g` respects the categorical α-equivalence `AbsRel X`. -/
theorem absRel_respect_of_swap {X : Nom} {Y : Type*} (g : Atom → X.obj.V → Y)
    (hswap : ∀ (a c : Atom) (x : X.obj.V) (s : Finset Atom),
      Supports X.obj s x → c ∉ s → c ≠ a → g a x = g c (X.obj.act (Equiv.swap a c) x)) :
    ∀ a a' x x', AbsRel X.obj (a, x) (a', x') → g a x = g a' x' := by
  intro a a' x x' hrel
  obtain ⟨w, hw⟩ := hrel
  obtain ⟨sx, hsx⟩ := X.property x
  obtain ⟨sx', hsx'⟩ := X.property x'
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (w ∪ sx ∪ sx' ∪ {a, a'})
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨⟨⟨hcw, hcsx⟩, hcsx'⟩, hca, hca'⟩ := hc
  have heq : X.obj.act (Equiv.swap a c) x = X.obj.act (Equiv.swap a' c) x' := hw c hcw
  rw [hswap a c x sx hsx hcsx hca, hswap a' c x' sx' hsx' hcsx' hca', heq]

/-- The eliminator built through the FCB (`absRel_respect_of_swap`). -/
def absRecOfSwap {X : Nom} {Y : Nom} (g : Atom → X.obj.V → Y.obj.V)
    (hg : ∀ (π : PermAtom) (a : Atom) (x : X.obj.V),
      g (π a) (X.obj.act π x) = Y.obj.act π (g a x))
    (hswap : ∀ (a c : Atom) (x : X.obj.V) (s : Finset Atom),
      Supports X.obj s x → c ∉ s → c ≠ a → g a x = g c (X.obj.act (Equiv.swap a c) x)) :
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
    (coreToNom β).obj.act (Equiv.swap (coreAtomEquiv a) (coreAtomEquiv c)) x
      = FinPerm.swap a c • x := by
  show fullSmul (fromPermℕ (Equiv.swap (coreAtomEquiv a) (coreAtomEquiv c))) x
      = FinPerm.swap a c • x
  rw [fromPermℕ_swap]
  exact fullSmul_val (FinPerm.swap a c) x

/-- The reconstructed action of `coreToNom β` on a transported `FinPerm` is the native action. -/
lemma coreToNom_finPerm_act (τ : FinPerm) (x : β) :
    (coreToNom β).obj.act (finPermToPerm τ) x = τ • x := by
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
  show (coreToNom β).obj.act (Equiv.swap (coreAtomEquiv a) d) x
      = (coreToNom β).obj.act (Equiv.swap (coreAtomEquiv a') d) x'
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
      = (absObj (coreToNom β)).obj.act (finPermToPerm τ) (coreAbsFwd β w) := by
  induction w using Quotient.inductionOn with
  | _ p =>
    obtain ⟨a, x⟩ := p
    show coreAbsFwd β (τ • abs a x)
        = (absGSet (coreToNom β).obj).act (finPermToPerm τ) (coreAbsFwd β (abs a x))
    rw [smul_abs]
    show absPt (coreToNom β).obj (coreAtomEquiv (τ • a)) (τ • x)
        = (absGSet (coreToNom β).obj).act (finPermToPerm τ)
            (absPt (coreToNom β).obj (coreAtomEquiv a) x)
    rw [absGSet_ρ_mk]
    have h1 : coreAtomEquiv (τ • a) = finPermToPerm τ (coreAtomEquiv a) := by
      have hsa : (τ • a) = τ.val a := rfl
      rw [hsa]
      simp only [finPermToPerm, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.permCongr_apply,
        Equiv.symm_apply_apply]
    have h2 : (τ • x : β) = (coreToNom β).obj.act (finPermToPerm τ) x :=
      (coreToNom_finPerm_act τ x).symm
    rw [h1, h2]

/-- **Equivariance** of the forward map against the reconstructed full-`Perm` actions on both
sides. Reduces the full permutation to a `FinPerm` agreeing on the relevant supports, then applies
`coreAbs_finPerm`. -/
lemma coreAbs_equiv (π : PermAtom) (w : NameAbs β) :
    coreAbsFwd β ((coreToNom (NameAbs β)).obj.act π w)
      = (absObj (coreToNom β)).obj.act π (coreAbsFwd β w) := by
  obtain ⟨sx, hsx⟩ := (coreToNom (NameAbs β)).property w
  obtain ⟨sy, hsy⟩ := (absObj (coreToNom β)).property (coreAbsFwd β w)
  obtain ⟨τ, hτ⟩ := finPermToPerm_agree_on_finset π (sx ∪ sy)
  have hx : (coreToNom (NameAbs β)).obj.act π w
      = (coreToNom (NameAbs β)).obj.act (finPermToPerm τ) w :=
    act_eq_of_supports hsx (fun a ha => (hτ a (Finset.mem_union_left sy ha)).symm)
  have hy : (absObj (coreToNom β)).obj.act (finPermToPerm τ) (coreAbsFwd β w)
      = (absObj (coreToNom β)).obj.act π (coreAbsFwd β w) :=
    act_eq_of_supports hsy (fun a ha => hτ a (Finset.mem_union_right sx ha))
  rw [hx, ← hy, coreToNom_finPerm_act, coreAbs_finPerm]

/-! ### The isomorphism -/

/-- The underlying `GSet` isomorphism `coreToNom (NameAbs β) ≅ absObj (coreToNom β)`. -/
noncomputable def coreAbsGSetIso (β : Type) [NomSet β] :
    (coreToNom (NameAbs β)).obj ≅ (absObj (coreToNom β)).obj :=
  Action.mkIso (Equiv.toIso (coreAbsEquiv β))
    (by
      intro π
      apply ConcreteCategory.hom_ext; intro w
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
