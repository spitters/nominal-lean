/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Nominal.Category.Nominal
public import Nominal.Category.NominalMonoidal
public import Nominal.Category.NominalAbstraction
public import Nominal.Category.NominalSeparatedExp

set_option autoImplicit false

/-!
# Phase 4 — the abstraction monomorphism `[𝔸]X ↪ 𝔸 ⊸ₛ X`

This file connects atom abstraction (`CatCrypt.Category.NominalAbstraction`) to the
monoidal-**closed** structure of `Nom`: it exhibits the name-abstraction object `[𝔸]X` as a
sub-object of the separated internal hom `𝔸 ⊸ₛ X` (`CatCrypt.Category.NominalSeparatedExp`).

The nominal-sets fact (Pitts, *Nominal Sets*) is that an abstraction `[a]x` **is** the partial
function `b ↦ (a b)·x`, defined off the support of `x`.  Concretely, `[a]x` maps to the
fresh-agreement class of the total finitely-supported function `b ↦ X.act (swap a b) x`.  Two
representatives `(a, x)`, `(a', x')` are α-equivalent exactly when these functions agree on all
fresh arguments, which is exactly fresh agreement — so the map is injective, i.e. a monomorphism.

## Main definitions

* `absToExpFun`, `absToExpCarrier` — the underlying total function `b ↦ X.act (swap a b) x` and its
  packaging as a finitely-supported function `funCarrier 𝔸 X` (supported by `insert a (supp x)`).
* `absToExpFn` — the map on quotients `[𝔸]X → (𝔸 ⊸ₛ X)`, sending `⟦(a, x)⟧` to the fresh-agreement
  class of `absToExpCarrier a x`; well defined by `absToExp_freshAgree`.
* `absToExp X : [𝔸]X ⟶ (𝔸 ⊸ₛ X)` — the equivariant morphism (an `Action.Hom` wrapped for `Nom`).

## Main results

* `absToExp_freshAgree` — α-equivalence of representatives implies fresh agreement of the
  associated functions (well-definedness of the quotient map).
* `absToExpCarrier_smul` — the map's building block is equivariant on the nose:
  `π • (b ↦ swap a b · x) = (b ↦ swap (π a) b · (π · x))`; used for the `comm` field.
* `absToExpFn_injective` / `absToExp_mono` — the map is injective, hence a monomorphism: distinct
  abstractions give distinct partial functions.

All results are axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

@[expose] public section

open CategoryTheory

namespace Nominal

set_option maxHeartbeats 800000

/-! ## Atoms: membership in the least support -/

/-- A finite set supporting an atom (in `atomGSet`) must contain it. -/
lemma atomGSet_supports_mem {s : Finset Atom} {a : Atom} (hsupp : Supports atomGSet s a) :
    a ∈ s := by
  by_contra ha
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (insert a s)
  rw [Finset.mem_insert, not_or] at hc
  obtain ⟨hca, hcs⟩ := hc
  have hfix : atomGSet.act (Equiv.swap a c) a = a :=
    hsupp (Equiv.swap a c) (fun e he =>
      Equiv.swap_apply_of_ne_of_ne (fun hh => ha (hh ▸ he)) (fun hh => hcs (hh ▸ he)))
  rw [show atomGSet.act (Equiv.swap a c) a = Equiv.swap a c a from rfl,
    Equiv.swap_apply_left] at hfix
  exact hca hfix

/-- Every atom lies in its own least support. -/
lemma atom_mem_supp (b : Atom) : b ∈ supp atomObj.property b :=
  atomGSet_supports_mem (supp_supports atomObj.property b)

/-! ## The underlying partial function `b ↦ swap a b · x` -/

/-- The total function underlying the abstraction `[a]x`: `b ↦ X.act (swap a b) x`. -/
def absToExpFun (X : Nom) (a : Atom) (x : X.obj.V) : atomObj.obj.V → X.obj.V :=
  fun b => X.obj.act (Equiv.swap a b) x

/-- The function `b ↦ swap a b · x` is finitely supported (for the conjugation action):
if `s` supports `x` then `insert a s` supports it. -/
lemma absToExpFun_supported (X : Nom) {s : Finset Atom} {a : Atom} {x : X.obj.V}
    (hs : Supports X.obj s x) :
    Supports (funGSetFull atomObj.obj X.obj) (insert a s) (absToExpFun X a x) := by
  intro π hπ
  funext b
  have hπa : π a = a := hπ a (Finset.mem_insert_self a s)
  have hx : X.obj.act π x = x := hs π (fun c hc => hπ c (Finset.mem_insert_of_mem hc))
  show X.obj.act π (X.obj.act (Equiv.swap a (π⁻¹ b)) x) = X.obj.act (Equiv.swap a b) x
  have hpi : π (π⁻¹ b) = b := by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have hperm : π * Equiv.swap a (π⁻¹ b) = Equiv.swap a b * π := by
    rw [← swap_mul_perm π a (π⁻¹ b), hπa, hpi]
  rw [← GSet.act_mul, hperm, GSet.act_mul, hx]

/-- The abstraction `[a]x` as a finitely-supported function in `funCarrier 𝔸 X`. -/
noncomputable def absToExpCarrier (X : Nom) (a : Atom) (x : X.obj.V) :
    funCarrier atomObj.obj X.obj :=
  ⟨absToExpFun X a x,
    insert a (X.property x).choose, absToExpFun_supported X (X.property x).choose_spec⟩

/-! ## Well-definedness: α-equivalence implies fresh agreement -/

/-- **Well-definedness.**  α-equivalent representatives `(a, x) ~ (a', x')` give fresh-agreement
equivalent functions.  Given a fresh argument `b` (separated from both least supports), we pick a
fresh atom `c` outside the α-equivalence witness set and both supports, use α-equivalence at `c`
(`f c = g c`), and transport back to `b` via the determined-by-fresh recovery. -/
lemma absToExp_freshAgree (X : Nom) {p q : Atom × X.obj.V} (h : AbsRel X.obj p q) :
    freshAgree atomObj X (absToExpCarrier X p.1 p.2) (absToExpCarrier X q.1 q.2) := by
  obtain ⟨s, hs⟩ := h
  show ∀ b : Atom, Disjoint (fsupp atomObj X (absToExpCarrier X p.1 p.2)
      ∪ fsupp atomObj X (absToExpCarrier X q.1 q.2)) (supp atomObj.property b)
      → (absToExpCarrier X p.1 p.2).1 b = (absToExpCarrier X q.1 q.2).1 b
  intro b hb
  set f := absToExpCarrier X p.1 p.2 with hf
  set g := absToExpCarrier X q.1 q.2 with hg
  -- `b` is fresh for both functions
  have hbmem : b ∈ supp atomObj.property b := atom_mem_supp b
  have hbfg : b ∉ fsupp atomObj X f ∪ fsupp atomObj X g :=
    fun hbin => (Finset.disjoint_left.mp hb hbin) hbmem
  have hbf : b ∉ fsupp atomObj X f :=
    fun hbin => hbfg (Finset.mem_union_left (fsupp atomObj X g) hbin)
  have hbg : b ∉ fsupp atomObj X g :=
    fun hbin => hbfg (Finset.mem_union_right (fsupp atomObj X f) hbin)
  -- choose a fresh atom `c`
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (insert b (s ∪ fsupp atomObj X f ∪ fsupp atomObj X g))
  have hcs : c ∉ s := fun h => hc (Finset.mem_insert_of_mem
    (Finset.mem_union_left (fsupp atomObj X g) (Finset.mem_union_left (fsupp atomObj X f) h)))
  have hcf : c ∉ fsupp atomObj X f := fun h => hc (Finset.mem_insert_of_mem
    (Finset.mem_union_left (fsupp atomObj X g) (Finset.mem_union_right s h)))
  have hcg : c ∉ fsupp atomObj X g := fun h => hc (Finset.mem_insert_of_mem
    (Finset.mem_union_right (s ∪ fsupp atomObj X f) h))
  -- least supports support the underlying functions
  have hSf : Supports (funGSetFull atomObj.obj X.obj) (fsupp atomObj X f) f.1 :=
    funGSet_supports_val (fsupp_supports atomObj X f)
  have hSg : Supports (funGSetFull atomObj.obj X.obj) (fsupp atomObj X g) g.1 :=
    funGSet_supports_val (fsupp_supports atomObj X g)
  have hπf : ∀ e ∈ fsupp atomObj X f, (Equiv.swap b c) e = e := fun e he =>
    Equiv.swap_apply_of_ne_of_ne (fun hh => hbf (hh ▸ he)) (fun hh => hcf (hh ▸ he))
  have hπg : ∀ e ∈ fsupp atomObj X g, (Equiv.swap b c) e = e := fun e he =>
    Equiv.swap_apply_of_ne_of_ne (fun hh => hbg (hh ▸ he)) (fun hh => hcg (hh ▸ he))
  have hbc : atomObj.obj.act (Equiv.swap b c) b = c := Equiv.swap_apply_left b c
  have ef : f.1 b = X.obj.act (Equiv.swap b c)⁻¹ (f.1 c) := by
    have hr := funGSetFull_recover hSf hπf b
    rwa [hbc] at hr
  have eg : g.1 b = X.obj.act (Equiv.swap b c)⁻¹ (g.1 c) := by
    have hr := funGSetFull_recover hSg hπg b
    rwa [hbc] at hr
  have hcval : f.1 c = g.1 c := hs c hcs
  rw [ef, eg, hcval]

/-! ## The quotient map and its equivariance -/

/-- The map on quotients `[𝔸]X → (𝔸 ⊸ₛ X)`: `⟦(a, x)⟧ ↦ ⟦b ↦ swap a b · x⟧`. -/
noncomputable def absToExpFn (X : Nom) : (absGSet X.obj).V → (sepExpGSet atomObj X).V :=
  Quotient.lift (fun p => Quotient.mk (freshAgreeSetoid atomObj X) (absToExpCarrier X p.1 p.2))
    (fun _ _ h => Quotient.sound (absToExp_freshAgree X h))

/-- Equivariance of the building block: `π • (b ↦ swap a b · x) = (b ↦ swap (π a) b · (π · x))`
as elements of the internal hom.  This is an *equality* (not just fresh agreement). -/
lemma absToExpCarrier_smul (X : Nom) (π : PermAtom) (a : Atom) (x : X.obj.V) :
    (funGSet atomObj.obj X.obj).act π (absToExpCarrier X a x)
      = absToExpCarrier X (π a) (X.obj.act π x) := by
  apply Subtype.ext
  funext b
  show (funGSetFull atomObj.obj X.obj).act π (absToExpFun X a x) b
      = X.obj.act (Equiv.swap (π a) b) (X.obj.act π x)
  rw [funGSetFull_ρ]
  show X.obj.act π (X.obj.act (Equiv.swap a (π⁻¹ b)) x)
      = X.obj.act (Equiv.swap (π a) b) (X.obj.act π x)
  have hpi : π (π⁻¹ b) = b := by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have hperm : π * Equiv.swap a (π⁻¹ b) = Equiv.swap (π a) b * π := by
    rw [← swap_mul_perm π a (π⁻¹ b), hpi]
  rw [← GSet.act_mul, hperm, GSet.act_mul]

/-- Underlying `Action.Hom` of the abstraction monomorphism. -/
noncomputable def absToExpActionHom (X : Nom) : absGSet X.obj ⟶ sepExpGSet atomObj X where
  hom := TypeCat.ofHom (absToExpFn X)
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro qq
    induction qq using Quotient.inductionOn with
    | _ pr =>
      obtain ⟨a, x⟩ := pr
      show absToExpFn X ((absGSet X.obj).act π (absPt X.obj a x))
          = (sepExpGSet atomObj X).act π (absToExpFn X (absPt X.obj a x))
      rw [absGSet_ρ_mk]
      show Quotient.mk (freshAgreeSetoid atomObj X) (absToExpCarrier X (π a) (X.obj.act π x))
          = (sepExpGSet atomObj X).act π
              (Quotient.mk (freshAgreeSetoid atomObj X) (absToExpCarrier X a x))
      rw [sepExpGSet_ρ_mk, absToExpCarrier_smul]

/-- **The abstraction map** `[𝔸]X ⟶ (𝔸 ⊸ₛ X)`. -/
noncomputable def absToExp (X : Nom) : absObj X ⟶ (atomObj ⊸ₛ X) :=
  ObjectProperty.homMk (absToExpActionHom X)

/-! ## Injectivity and the monomorphism -/

/-- **Injectivity — the mathematical content.**  Distinct abstractions give distinct partial
functions.  If `⟦b ↦ swap a b · x⟧ = ⟦b ↦ swap a' b · x'⟧` (fresh agreement), then the functions
agree on every atom `c` outside `fsupp f ∪ fsupp g`, which is exactly an α-equivalence witness. -/
lemma absToExpFn_injective (X : Nom) : Function.Injective (absToExpFn X) := by
  intro X1 X2
  refine Quotient.inductionOn₂ X1 X2 ?_
  intro p q hX
  have hfa : freshAgree atomObj X (absToExpCarrier X p.1 p.2) (absToExpCarrier X q.1 q.2) :=
    Quotient.exact hX
  apply Quotient.sound
  show AbsRel X.obj p q
  refine ⟨fsupp atomObj X (absToExpCarrier X p.1 p.2)
      ∪ fsupp atomObj X (absToExpCarrier X q.1 q.2), fun c hc => ?_⟩
  have hsuppc : supp atomObj.property c ⊆ ({c} : Finset Atom) :=
    supp_le atomObj.property (fun _ hπ => hπ c (Finset.mem_singleton_self c))
  have hdisj : Disjoint (fsupp atomObj X (absToExpCarrier X p.1 p.2)
      ∪ fsupp atomObj X (absToExpCarrier X q.1 q.2)) (supp atomObj.property c) := by
    rw [Finset.disjoint_left]
    intro y hy hyc
    have hyeq : y = c := Finset.mem_singleton.mp (hsuppc hyc)
    rw [hyeq] at hy
    exact hc hy
  exact hfa c hdisj

/-- **The abstraction map is a monomorphism** `[𝔸]X ↪ (𝔸 ⊸ₛ X)`. -/
theorem absToExp_mono (X : Nom) : Mono (absToExp X) := by
  constructor
  intro Z g h hgh
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext; intro z
  apply absToExpFn_injective X
  simpa only [ConcreteCategory.comp_apply] using!
    congrArg (fun m : Z ⟶ atomObj ⊸ₛ X => ConcreteCategory.hom m.hom.hom z) hgh

end Nominal
