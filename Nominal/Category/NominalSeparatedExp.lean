/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.NominalMonoidalClosedFull

set_option autoImplicit false

/-!
# M3, part 3 — the separated exponential `B ⊸ₛ C` as a fresh-agreement quotient

`CatCrypt.Category.NominalMonoidalClosedFull` proved (`uncurry_not_injective`) that the total
finitely-supported function space `funObj` (`B ⊸ₙ C`) is **not** the right adjoint of the separated
tensor `· ⊗ₙ B`: it is `Nom`'s cartesian exponential, and `uncurry` is not injective on it because
two functions with equal *fresh* restrictions can differ off the separated locus.

`Nom` under the separated product `⊗ₙ` is symmetric monoidal closed (Pitts, *Nominal Sets*); the
correct internal hom is the **separated / fresh function space**.  This file builds it as the
quotient of `funGSet B C` by the *fresh-agreement* equivalence — the counterexample directly
motivates the quotient: it identifies exactly the pairs that `uncurry_not_injective` exhibits.

## Scope

* **Freshness / avoidance** (`exists_avoiding_perm`): a permutation fixing one finite set pointwise
  and moving another (disjoint) finite set entirely off a third.  This is the fresh-renaming core.
* **Equivariance of least support** (`supp_smul`): `supp (ρ π x) = (supp x).image π`.
* **The fresh-agreement equivalence** (`freshAgree`, `freshAgreeSetoid`): `f ≈ g` iff `f` and `g`
  agree on every argument fresh for both least supports.  Proved reflexive, symmetric, and — via
  `exists_avoiding_perm` — transitive, and an action congruence (`freshAgree_congr`).
* **The separated exponential object** (`sepExpObj`, notation `B ⊸ₛ C`): `funGSet B C / ≈` as a
  nominal set, with its conjugation action and finite-support proof.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

open CategoryTheory

open scoped Classical

namespace Nominal

/-- Group-inverse cancellation as function application: `π (π⁻¹ x) = x`. -/
private lemma perm_apply_inv (π : PermAtom) (x : Atom) : π (π⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

/-! ### Freshness and avoidance -/

/-- **Avoidance / fresh renaming.**  Given a `Fix`ed finite set, a set `Avoid` to steer clear of,
and a `Move` set disjoint from `Fix`, there is a permutation fixing `Fix` pointwise that carries
every element of `Move` outside `Avoid`.  Proved by induction on `Move`, swapping each element with
a fresh atom outside `Avoid ∪ Fix ∪ σ(Move)`. -/
lemma exists_avoiding_perm (Fix Avoid : Finset Atom) :
    ∀ Move : Finset Atom, Disjoint Move Fix →
      ∃ π : PermAtom, (∀ a ∈ Fix, π a = a) ∧ ∀ a ∈ Move, π a ∉ Avoid := by
  intro Move
  induction Move using Finset.induction with
  | empty => exact fun _ => ⟨1, fun _ _ => rfl, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  | @insert a M ha IH =>
    intro hdisj
    have haFix : a ∉ Fix :=
      fun h => (Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a M)) h
    have hMFix : Disjoint M Fix := hdisj.mono_left (Finset.subset_insert a M)
    obtain ⟨σ, hσfix, hσM⟩ := IH hMFix
    have hσaFix : σ a ∉ Fix := by
      intro hmem
      have h1 : σ (σ a) = σ a := hσfix (σ a) hmem
      have h2 : σ a = a := σ.injective h1
      exact haFix (h2 ▸ hmem)
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (Avoid ∪ Fix ∪ (insert a M).image σ)
    rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at hc
    obtain ⟨⟨hcAvoid, hcFix⟩, hcImg⟩ := hc
    refine ⟨Equiv.swap (σ a) c * σ, ?_, ?_⟩
    · intro x hx
      have hσx : σ x = x := hσfix x hx
      rw [Equiv.Perm.mul_apply, hσx]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; exact hσaFix (h ▸ hx)
      · intro h; exact hcFix (h ▸ hx)
    · intro x hx
      rw [Equiv.Perm.mul_apply]
      rcases Finset.mem_insert.mp hx with rfl | hxM
      · rw [Equiv.swap_apply_left]; exact hcAvoid
      · have hσx : σ x ∉ Avoid := hσM x hxM
        have hxa : x ≠ a := fun h => ha (h ▸ hxM)
        have hne1 : σ x ≠ σ a := fun h => hxa (σ.injective h)
        have hne2 : σ x ≠ c :=
          fun h => hcImg (Finset.mem_image.mpr ⟨x, Finset.mem_insert_of_mem hxM, h⟩)
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]; exact hσx

/-! ### Equivariance of least support -/

/-- The least support is equivariant: `supp (ρ π x) = (supp x).image π`. -/
lemma supp_smul {A : GSet} (hA : IsNominal A) (π : PermAtom) (x : A.V) :
    supp hA (A.act π x) = (supp hA x).image π := by
  apply Finset.Subset.antisymm
  · exact supp_le hA ((supp_supports hA x).smul π)
  · have hx : A.act π⁻¹ (A.act π x) = x := by
      rw [← GSet.act_mul, inv_mul_cancel, GSet.act_one]
    have h1 : supp hA x ⊆ (supp hA (A.act π x)).image (π⁻¹ : PermAtom) := by
      have hsm := (supp_supports hA (A.act π x)).smul π⁻¹
      rw [hx] at hsm
      exact supp_le hA hsm
    calc (supp hA x).image π
        ⊆ ((supp hA (A.act π x)).image (π⁻¹ : PermAtom)).image π :=
          Finset.image_subset_image h1
      _ = supp hA (A.act π x) := by
          rw [Finset.image_image]
          have hcomp : (π : Atom → Atom) ∘ (π⁻¹ : PermAtom) = id := by
            funext y; exact perm_apply_inv π y
          rw [hcomp, Finset.image_id]

/-- A support of `f` as an element of `funGSet` supports the underlying function `f.1` for the
conjugation action on `funGSetFull`. -/
lemma funGSet_supports_val {B C : GSet} {s : Finset Atom} {f : funCarrier B C}
    (h : Supports (funGSet B C) s f) : Supports (funGSetFull B C) s f.1 := by
  intro π hπ
  have h2 := congrArg Subtype.val (h π hπ)
  rwa [funGSet_ρ_coe] at h2

/-- Disjointness transports across an injective image: `Disjoint (S.image π) T` gives
`Disjoint S (T.image π⁻¹)`. -/
lemma disjoint_image_perm {S T : Finset Atom} {π : PermAtom}
    (h : Disjoint (S.image π) T) : Disjoint S (T.image (π⁻¹ : PermAtom)) := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  rw [Finset.mem_image] at hxT
  obtain ⟨t, htT, hpt⟩ := hxT
  have hmem : π x ∈ S.image π := Finset.mem_image_of_mem π hxS
  have hπx : π x = t := by rw [← hpt, perm_apply_inv]
  rw [hπx] at hmem
  exact Finset.disjoint_left.mp h hmem htT

/-! ### The fresh-agreement equivalence -/

/-- Least support of a finitely supported function, as an element of the internal-hom nominal set
`funGSet B C`. -/
noncomputable def fsupp (B C : Nom) (f : funCarrier B.obj C.obj) : Finset Atom :=
  supp (funGSet_isNominal B.obj C.obj) f

/-- Equivariance of the internal-hom least support. -/
lemma fsupp_smul (B C : Nom) (π : PermAtom) (f : funCarrier B.obj C.obj) :
    fsupp B C ((funGSet B.obj C.obj).act π f) = (fsupp B C f).image π :=
  supp_smul (funGSet_isNominal B.obj C.obj) π f

/-- The internal-hom least support is a support. -/
lemma fsupp_supports (B C : Nom) (f : funCarrier B.obj C.obj) :
    Supports (funGSet B.obj C.obj) (fsupp B C f) f :=
  supp_supports (funGSet_isNominal B.obj C.obj) f

/-- A permutation fixing `Fix` keeps the image of a `Fix`-disjoint set clear of `Fix`. -/
lemma image_disjoint_of_fix {Fix Move : Finset Atom} {π : PermAtom}
    (hfix : ∀ a ∈ Fix, π a = a) (hd : Disjoint Move Fix) :
    Disjoint (Move.image π) Fix := by
  rw [Finset.disjoint_left]; intro y hy hyF
  rw [Finset.mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy
  have h1 : π (π x) = π x := hfix (π x) hyF
  have h2 : π x = x := π.injective h1
  rw [h2] at hyF
  exact Finset.disjoint_left.mp hd hx hyF

/-- **Fresh agreement.**  `f` and `g` agree on every argument `b` that is *fresh* (separated) from
both least supports.  This is the equivalence whose quotient is the separated exponential: it
identifies exactly the functions with equal fresh restrictions. -/
def freshAgree (B C : Nom) (f g : funCarrier B.obj C.obj) : Prop :=
  ∀ b : B.obj.V, Disjoint (fsupp B C f ∪ fsupp B C g) (supp B.property b) → f.1 b = g.1 b

lemma freshAgree_refl (B C : Nom) (f : funCarrier B.obj C.obj) : freshAgree B C f f :=
  fun _ _ => rfl

lemma freshAgree_symm {B C : Nom} {f g : funCarrier B.obj C.obj}
    (h : freshAgree B C f g) : freshAgree B C g f := by
  intro b hb
  rw [Finset.union_comm] at hb
  exact (h b hb).symm

/-- **Transitivity** of fresh agreement — the load-bearing step.  Given `b` fresh for `supp f` and
`supp g`, `exists_avoiding_perm` produces a support-fixing renaming `π` (fixing `supp f ∪ supp h`)
that carries `b` off `supp g` as well; there `f ≈ g` and `g ≈ h` chain, and the values transport
back by the conjugation equivariance `funGSetFull_apply_of_supports`. -/
lemma freshAgree_trans {B C : Nom} {f g h : funCarrier B.obj C.obj}
    (hfg : freshAgree B C f g) (hgh : freshAgree B C g h) : freshAgree B C f h := by
  intro b hb
  set sf := fsupp B C f with hsf
  set sg := fsupp B C g with hsg
  set sh := fsupp B C h with hsh
  set sb := supp B.property b with hsb
  -- avoidance renaming: fix `sf ∪ sh`, move `sb` off `sg ∪ sf ∪ sh`.
  obtain ⟨π, hπfix, hπav⟩ :=
    exists_avoiding_perm (sf ∪ sh) (sg ∪ sf ∪ sh) sb hb.symm
  set b' := B.obj.act π b with hb'
  have hsb' : supp B.property b' = sb.image π := supp_smul B.property π b
  -- `b'` is separated from `sg`, `sf`, `sh`.
  have hb'av : Disjoint (supp B.property b') (sg ∪ sf ∪ sh) := by
    rw [hsb', Finset.disjoint_left]
    intro y hy hy2
    rw [Finset.mem_image] at hy
    obtain ⟨a, haM, rfl⟩ := hy
    exact hπav a haM hy2
  -- supports of the underlying functions
  have hSf : Supports (funGSetFull B.obj C.obj) sf f.1 :=
    funGSet_supports_val (hsf ▸ supp_supports (funGSet_isNominal B.obj C.obj) f)
  have hSh : Supports (funGSetFull B.obj C.obj) sh h.1 :=
    funGSet_supports_val (hsh ▸ supp_supports (funGSet_isNominal B.obj C.obj) h)
  have hπf : ∀ x ∈ sf, π x = x := fun x hx => hπfix x (Finset.mem_union_left sh hx)
  have hπh : ∀ x ∈ sh, π x = x := fun x hx => hπfix x (Finset.mem_union_right sf hx)
  -- transport the values of `f` and `h` between `b` and `b'`
  have hfb' : f.1 b' = C.obj.act π (f.1 b) := funGSetFull_apply_of_supports hSf hπf b
  have hhb' : h.1 b' = C.obj.act π (h.1 b) := funGSetFull_apply_of_supports hSh hπh b
  -- chain `f ≈ g ≈ h` at the fresh point `b'`
  have hsub_fg : sf ∪ sg ⊆ sg ∪ sf ∪ sh := by intro x; simp only [Finset.mem_union]; tauto
  have hsub_gh : sg ∪ sh ⊆ sg ∪ sf ∪ sh := by intro x; simp only [Finset.mem_union]; tauto
  have hfg' : f.1 b' = g.1 b' := hfg b' (hb'av.symm.mono_left hsub_fg)
  have hgh' : g.1 b' = h.1 b' := hgh b' (hb'av.symm.mono_left hsub_gh)
  have hval : f.1 b' = h.1 b' := hfg'.trans hgh'
  rw [hfb', hhb'] at hval
  have : C.obj.act π⁻¹ (C.obj.act π (f.1 b)) = C.obj.act π⁻¹ (C.obj.act π (h.1 b)) := by rw [hval]
  rwa [← GSet.act_mul, ← GSet.act_mul, inv_mul_cancel, GSet.act_one, GSet.act_one] at this

/-- **Action congruence.**  Fresh agreement is stable under the conjugation action, so the quotient
carries a `PermAtom` action. -/
lemma freshAgree_congr {B C : Nom} {f g : funCarrier B.obj C.obj}
    (hfg : freshAgree B C f g) (π : PermAtom) :
    freshAgree B C ((funGSet B.obj C.obj).act π f) ((funGSet B.obj C.obj).act π g) := by
  intro b' hb'
  -- rewrite the supports of the shifted functions via `supp_smul`
  have hsuppf : fsupp B C ((funGSet B.obj C.obj).act π f) = (fsupp B C f).image π :=
    supp_smul (funGSet_isNominal B.obj C.obj) π f
  have hsuppg : fsupp B C ((funGSet B.obj C.obj).act π g) = (fsupp B C g).image π :=
    supp_smul (funGSet_isNominal B.obj C.obj) π g
  rw [hsuppf, hsuppg, ← Finset.image_union] at hb'
  set b := B.obj.act π⁻¹ b' with hbdef
  have hsuppb : supp B.property b = (supp B.property b').image (π⁻¹ : PermAtom) :=
    supp_smul B.property π⁻¹ b'
  have hdisj : Disjoint (fsupp B C f ∪ fsupp B C g) (supp B.property b) := by
    rw [hsuppb]; exact disjoint_image_perm hb'
  have hval : f.1 b = g.1 b := hfg b hdisj
  show (funGSetFull B.obj C.obj).act π f.1 b' = (funGSetFull B.obj C.obj).act π g.1 b'
  simp only [funGSetFull_ρ]
  rw [hbdef] at hval
  rw [hval]

/-- The fresh-agreement setoid on the internal-hom carrier. -/
def freshAgreeSetoid (B C : Nom) : Setoid (funCarrier B.obj C.obj) where
  r := freshAgree B C
  iseqv := ⟨freshAgree_refl B C, freshAgree_symm, freshAgree_trans⟩

/-! ### The separated exponential object `B ⊸ₛ C` -/

/-- Carrier of the separated exponential: fresh-agreement classes of finitely supported functions. -/
def sepExpCarrier (B C : Nom) : Type := Quotient (freshAgreeSetoid B C)

/-- The conjugation action descends to the quotient by `freshAgree_congr`. -/
def sepExpGSet (B C : Nom) : GSet where
  V := sepExpCarrier B C
  ρ :=
    { toFun := fun π => TypeCat.ofHom (Quotient.lift
        (fun f => Quotient.mk (freshAgreeSetoid B C) ((funGSet B.obj C.obj).act π f))
        (fun _ _ hfg => Quotient.sound (freshAgree_congr hfg π)))
      map_one' := by
        apply ConcreteCategory.hom_ext; intro X
        induction X using Quotient.inductionOn with
        | _ f =>
          show Quotient.mk _ ((funGSet B.obj C.obj).act 1 f) = Quotient.mk _ f
          rw [GSet.act_one]; rfl
      map_mul' := fun a b => by
        apply ConcreteCategory.hom_ext; intro X
        induction X using Quotient.inductionOn with
        | _ f =>
          show Quotient.mk _ ((funGSet B.obj C.obj).act (a * b) f)
            = Quotient.mk _ ((funGSet B.obj C.obj).act a ((funGSet B.obj C.obj).act b f))
          rw [GSet.act_mul] }

@[simp] lemma sepExpGSet_ρ_mk (B C : Nom) (π : PermAtom) (f : funCarrier B.obj C.obj) :
    (sepExpGSet B C).act π (Quotient.mk (freshAgreeSetoid B C) f)
      = Quotient.mk (freshAgreeSetoid B C) ((funGSet B.obj C.obj).act π f) := rfl

/-- The separated exponential is nominal: the class `⟦f⟧` is supported by `supp f`. -/
lemma sepExpGSet_isNominal (B C : Nom) : IsNominal (sepExpGSet B C) := by
  intro X
  induction X using Quotient.inductionOn with
  | _ f =>
    refine ⟨fsupp B C f, ?_⟩
    intro π hπ
    have hfix : (funGSet B.obj C.obj).act π f = f :=
      (supp_supports (funGSet_isNominal B.obj C.obj) f) π hπ
    show (sepExpGSet B C).act π (Quotient.mk _ f) = Quotient.mk _ f
    rw [sepExpGSet_ρ_mk, hfix]

/-- The **separated exponential** `B ⊸ₛ C : Nom`. -/
def sepExpObj (B C : Nom) : Nom :=
  Nom.of (sepExpGSet B C) (sepExpGSet_isNominal B C)

@[inherit_doc] infixr:70 " ⊸ₛ " => sepExpObj

/-- The class `⟦f⟧` is supported by any support of the representative `f`. -/
lemma sepExp_mk_supported (B C : Nom) (f : funCarrier B.obj C.obj) :
    Supports (sepExpGSet B C) (fsupp B C f) (Quotient.mk (freshAgreeSetoid B C) f) := by
  intro π hπ
  have hfix : (funGSet B.obj C.obj).act π f = f :=
    (supp_supports (funGSet_isNominal B.obj C.obj) f) π hπ
  show (sepExpGSet B C).act π (Quotient.mk _ f) = Quotient.mk _ f
  rw [sepExpGSet_ρ_mk, hfix]

/-- Injective images preserve disjointness. -/
lemma disjoint_image_image {S T : Finset Atom} (π : PermAtom) (hd : Disjoint S T) :
    Disjoint (S.image π) (T.image π) := by
  rw [Finset.disjoint_left]; intro y hyS hyT
  rw [Finset.mem_image] at hyS hyT
  obtain ⟨x, hx, rfl⟩ := hyS
  obtain ⟨x', hx', hx'y⟩ := hyT
  have hxx : x' = x := π.injective hx'y
  subst hxx
  exact Finset.disjoint_left.mp hd hx hx'

/-! ### Step 3 — the separated evaluation and `uncurryQ`

To transpose a morphism `h : A ⟶ B ⊸ₛ C` into `A ⊗ₙ B ⟶ C` we must evaluate the class `h a` at a
separated argument `b`.  Because `uncurry_not_injective` shows evaluation of an *arbitrary*
representative at an argument fresh only for the class support is ill defined, we first move to a
representative whose *own* support avoids `b` (`exists_fresh_rep`), where the value is determined
(`evalCls`, `evalCls_eq`). -/

/-- **Fresh representative.**  A class supported by `s`, evaluated at a `b` fresh for `s`, has a
representative whose least support also avoids `b`.  Built by an avoidance renaming fixing the
class support and pushing the rest of a representative's support off `supp b`. -/
lemma exists_fresh_rep (B C : Nom) (X : sepExpCarrier B C) (b : B.obj.V) {s : Finset Atom}
    (hs : Supports (sepExpGSet B C) s X) (hsb : Disjoint s (supp B.property b)) :
    ∃ f : funCarrier B.obj C.obj,
      Quotient.mk (freshAgreeSetoid B C) f = X ∧ Disjoint (fsupp B C f) (supp B.property b) := by
  induction X using Quotient.inductionOn with
  | _ f0 =>
    set sb := supp B.property b with hsbdef
    set sX := supp (sepExpGSet_isNominal B C) (Quotient.mk (freshAgreeSetoid B C) f0) with hsX
    have hsXb : Disjoint sX sb := hsb.mono_left (supp_le (sepExpGSet_isNominal B C) hs)
    have hsX_sub : sX ⊆ fsupp B C f0 :=
      supp_le (sepExpGSet_isNominal B C) (sepExp_mk_supported B C f0)
    obtain ⟨π, hπfix, hπav⟩ :=
      exists_avoiding_perm sX sb (fsupp B C f0 \ sX) Finset.sdiff_disjoint
    refine ⟨(funGSet B.obj C.obj).act π f0, ?_, ?_⟩
    · have hXfix : (sepExpGSet B C).act π (Quotient.mk _ f0) = Quotient.mk _ f0 :=
        (supp_supports (sepExpGSet_isNominal B C) (Quotient.mk _ f0)) π hπfix
      rwa [sepExpGSet_ρ_mk] at hXfix
    · rw [fsupp_smul]
      have hunion : sX ∪ (fsupp B C f0 \ sX) = fsupp B C f0 := by
        rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hsX_sub
      rw [← hunion, Finset.image_union]
      refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
      · have himg : sX.image π = sX := by
          apply Finset.Subset.antisymm
          · intro y hy; rw [Finset.mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy
            rw [hπfix x hx]; exact hx
          · intro x hx; rw [Finset.mem_image]; exact ⟨x, hx, hπfix x hx⟩
        rw [himg]; exact hsXb
      · rw [Finset.disjoint_left]; intro y hy hy2
        rw [Finset.mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy
        exact hπav x hx hy2

/-- Evaluation of a class at an argument fresh for one of its representatives. -/
noncomputable def evalCls (B C : Nom) (X : sepExpCarrier B C) (b : B.obj.V)
    (H : ∃ f : funCarrier B.obj C.obj,
      Quotient.mk (freshAgreeSetoid B C) f = X ∧ Disjoint (fsupp B C f) (supp B.property b)) :
    C.obj.V :=
  (Classical.choose H).1 b

/-- The evaluation agrees with **any** representative fresh for the argument. -/
lemma evalCls_eq (B C : Nom) (X : sepExpCarrier B C) (b : B.obj.V)
    (H : ∃ f : funCarrier B.obj C.obj,
      Quotient.mk (freshAgreeSetoid B C) f = X ∧ Disjoint (fsupp B C f) (supp B.property b))
    (g : funCarrier B.obj C.obj) (hgX : Quotient.mk (freshAgreeSetoid B C) g = X)
    (hgb : Disjoint (fsupp B C g) (supp B.property b)) :
    evalCls B C X b H = g.1 b := by
  have hspec := Classical.choose_spec H
  show (Classical.choose H).1 b = g.1 b
  have hfg : freshAgree B C (Classical.choose H) g :=
    Quotient.exact (hspec.1.trans hgX.symm)
  exact hfg b (Finset.disjoint_union_left.mpr ⟨hspec.2, hgb⟩)

/-- Underlying `Action.Hom` of the quotient uncurrying. -/
noncomputable def uncurryQActionHom {A B C : Nom} (h : A ⟶ B ⊸ₛ C) :
    sepGSet A.obj B.obj ⟶ C.obj where
  hom := TypeCat.ofHom fun p => evalCls B C (h.hom.hom p.1.1) p.1.2
    (exists_fresh_rep B C (h.hom.hom p.1.1) p.1.2
      (Supports.map h.hom (supp_supports A.property p.1.1))
      ((Separated_iff_disjoint A.property B.property p.1.1 p.1.2).mp p.2))
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro p
    obtain ⟨⟨a, b⟩, hsep⟩ := p
    -- a fresh representative `f` for `(h a, b)`
    obtain ⟨f, hfX, hfb⟩ := exists_fresh_rep B C (h.hom.hom a) b
      (Supports.map h.hom (supp_supports A.property a))
      ((Separated_iff_disjoint A.property B.property a b).mp hsep)
    -- `ρπ f` is a fresh representative for `(h (ρπ a), ρπ b)`
    have hcomm : h.hom.hom (A.obj.act π a) = (sepExpGSet B C).act π (h.hom.hom a) := by
      have := ConcreteCategory.congr_hom (h.hom.comm π) a
      simpa only [ConcreteCategory.comp_apply] using this
    have hfX' : Quotient.mk (freshAgreeSetoid B C) ((funGSet B.obj C.obj).act π f)
        = h.hom.hom (A.obj.act π a) := by
      rw [hcomm, ← hfX, sepExpGSet_ρ_mk]
    have hfb' : Disjoint (fsupp B C ((funGSet B.obj C.obj).act π f))
        (supp B.property (B.obj.act π b)) := by
      rw [fsupp_smul, supp_smul B.property π b]
      exact disjoint_image_image π hfb
    -- compute the shifted representative value
    have hshift : ((funGSet B.obj C.obj).act π f).1 (B.obj.act π b) = C.obj.act π (f.1 b) := by
      rw [funGSet_ρ_coe, funGSetFull_ρ, ← GSet.act_mul, inv_mul_cancel, GSet.act_one]
    show evalCls B C (h.hom.hom (A.obj.act π a)) (B.obj.act π b) _
        = C.obj.act π (evalCls B C (h.hom.hom a) b _)
    rw [evalCls_eq B C _ (B.obj.act π b) _ ((funGSet B.obj C.obj).act π f) hfX' hfb',
        evalCls_eq B C _ b _ f hfX hfb, hshift]

/-- **Quotient uncurrying**: transpose `A ⟶ (B ⊸ₛ C)` to `A ⊗ₙ B ⟶ C`.  This is the map that
`uncurry_not_injective` says cannot be inverted on `funObj`; on the quotient it is well defined. -/
noncomputable def uncurryQ {A B C : Nom} (h : A ⟶ B ⊸ₛ C) : A ⊗ₙ B ⟶ C :=
  ObjectProperty.homMk (uncurryQActionHom h)

/-- **The obstruction is resolved on the quotient: `uncurryQ` is injective.**  Where
`uncurry_not_injective` exhibits distinct morphisms into `funObj` with equal uncurryings,
`uncurryQ` on the separated exponential has no such collision.  Given `uncurryQ h = uncurryQ h'`,
to show `h a = h' a` (an equality of classes) we prove any representatives `f`, `f'` fresh-agree:
at a test argument `b` we rename (`exists_avoiding_perm`) to a separated `b''` where `f`/`f'` are
fresh, read off the shared `uncurryQ` value, and transport back by the conjugation equivariance. -/
theorem uncurryQ_injective {A B C : Nom} {h h' : A ⟶ B ⊸ₛ C}
    (heq : uncurryQ h = uncurryQ h') : h = h' := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext; intro a
  obtain ⟨f, hf⟩ := Quotient.exists_rep (h.hom.hom a)
  obtain ⟨f', hf'⟩ := Quotient.exists_rep (h'.hom.hom a)
  rw [← hf, ← hf']
  apply Quotient.sound
  intro b hb
  -- rename `b` off `supp a`, fixing `supp f ∪ supp f'`
  obtain ⟨π, hπfix, hπav⟩ :=
    exists_avoiding_perm (fsupp B C f ∪ fsupp B C f') (supp A.property a) (supp B.property b) hb.symm
  set b'' := B.obj.act π b with hb''
  have hsuppb'' : supp B.property b'' = (supp B.property b).image π := supp_smul B.property π b
  have hb''a : Disjoint (supp B.property b'') (supp A.property a) := by
    rw [hsuppb'', Finset.disjoint_left]; intro y hy hya
    rw [Finset.mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy
    exact hπav x hx hya
  have hsep : Separated A.obj B.obj a b'' :=
    (Separated_iff_disjoint A.property B.property a b'').mpr hb''a.symm
  -- `f`, `f'` are fresh for `b''`
  have hb''Fix : Disjoint ((supp B.property b).image π) (fsupp B C f ∪ fsupp B C f') :=
    image_disjoint_of_fix hπfix hb.symm
  have hfb'' : Disjoint (fsupp B C f) (supp B.property b'') := by
    rw [hsuppb'']; exact (hb''Fix.mono_right Finset.subset_union_left).symm
  have hf'b'' : Disjoint (fsupp B C f') (supp B.property b'') := by
    rw [hsuppb'']; exact (hb''Fix.mono_right Finset.subset_union_right).symm
  -- the shared `uncurryQ` value at the separated pair `(a, b'')`
  have hLHS : (uncurryQ h).hom.hom ⟨(a, b''), hsep⟩ = f.1 b'' :=
    evalCls_eq B C _ b'' _ f hf hfb''
  have hRHS : (uncurryQ h').hom.hom ⟨(a, b''), hsep⟩ = f'.1 b'' :=
    evalCls_eq B C _ b'' _ f' hf' hf'b''
  have hpair : (uncurryQ h).hom.hom ⟨(a, b''), hsep⟩ = (uncurryQ h').hom.hom ⟨(a, b''), hsep⟩ :=
    congrArg (fun m : A ⊗ₙ B ⟶ C => m.hom.hom ⟨(a, b''), hsep⟩) heq
  have hval'' : f.1 b'' = f'.1 b'' := by rw [← hLHS, ← hRHS]; exact hpair
  -- transport the value back from `b''` to `b`
  have hSf : Supports (funGSetFull B.obj C.obj) (fsupp B C f) f.1 :=
    funGSet_supports_val (fsupp_supports B C f)
  have hSf' : Supports (funGSetFull B.obj C.obj) (fsupp B C f') f'.1 :=
    funGSet_supports_val (fsupp_supports B C f')
  have hπf : ∀ x ∈ fsupp B C f, π x = x := fun x hx => hπfix x (Finset.mem_union_left _ hx)
  have hπf' : ∀ x ∈ fsupp B C f', π x = x := fun x hx => hπfix x (Finset.mem_union_right _ hx)
  have et1 : f.1 b'' = C.obj.act π (f.1 b) := funGSetFull_apply_of_supports hSf hπf b
  have et2 : f'.1 b'' = C.obj.act π (f'.1 b) := funGSetFull_apply_of_supports hSf' hπf' b
  rw [et1, et2] at hval''
  have hcancel := congrArg (C.obj.act π⁻¹) hval''
  rwa [← GSet.act_mul, ← GSet.act_mul, inv_mul_cancel, GSet.act_one, GSet.act_one] at hcancel

/-! ### Step 3, continued — `uncurry` factors through fresh agreement

The transpose `uncurry` into the *total*-function hom `funObj` inspects only separated pairs; two
morphisms whose pointwise images are fresh-agreement equivalent therefore have equal uncurryings.
This is exactly the factoring `uncurry_not_injective` calls for: on the quotient the transpose is
well defined. -/

/-- **The factoring.**  If `h, h' : A ⟶ B ⊸ₙ C` have pointwise fresh-agreement-equivalent images
(`h a ≈ h' a` for every `a`), then `uncurry h = uncurry h'`.  The proof: on a separated pair
`(a, b)`, the argument `b` is fresh for `supp a`, hence for both `supp (h a)` and `supp (h' a)`
(which sit inside `supp a` by equivariance), so fresh agreement forces `(h a).1 b = (h' a).1 b`. -/
lemma uncurry_respects_freshAgree {A B C : Nom} (h h' : A ⟶ B ⊸ₙ C)
    (hpt : ∀ a : A.obj.V, freshAgree B C (h.hom.hom a) (h'.hom.hom a)) :
    uncurry h = uncurry h' := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext; intro p
  simp only [uncurry_apply]
  obtain ⟨⟨a, b⟩, hsep⟩ := p
  refine hpt a b ?_
  have hab : Disjoint (supp A.property a) (supp B.property b) :=
    (Separated_iff_disjoint A.property B.property a b).mp hsep
  have hha : fsupp B C (h.hom.hom a) ⊆ supp A.property a :=
    supp_le (funGSet_isNominal B.obj C.obj) (Supports.map h.hom (supp_supports A.property a))
  have hh'a : fsupp B C (h'.hom.hom a) ⊆ supp A.property a :=
    supp_le (funGSet_isNominal B.obj C.obj) (Supports.map h'.hom (supp_supports A.property a))
  exact hab.mono_left (Finset.union_subset hha hh'a)

/-! ### Step 4 — the adjunction and `MonoidalClosed Nom`

What is established here, axiom-cleanly (`propext`, `Classical.choice`, `Quot.sound` only):

* the separated exponential **object** `B ⊸ₛ C` as the fresh-agreement quotient of `funGSet B C`,
  with its conjugation action and finite-support proof (`sepExpObj`, `sepExpGSet_isNominal`);
* the fresh-agreement relation is a genuine **action-stable equivalence** (`freshAgreeSetoid`,
  `freshAgree_trans`, `freshAgree_congr`), transitivity resting on the fresh-renaming
  `exists_avoiding_perm`;
* the transpose **`uncurryQ : (A ⟶ B ⊸ₛ C) → (A ⊗ₙ B ⟶ C)`** (a genuine equivariant morphism), and
* **`uncurryQ_injective`** — the exact resolution of `uncurry_not_injective`: on the quotient the
  transpose has no collision, together with `uncurry_respects_freshAgree` showing the collisions on
  `funObj` are *precisely* fresh agreement.

The adjunction `tensorRight B ⊣ (B ⊸ₛ ·)`, hence `Closed B` / `MonoidalClosed Nom`, is completed in
`CatCrypt.Category.NominalMonoidalClosedComplete` and registered there as
`Nominal.monoidalClosedNom`. The last ingredient it supplies is the inverse transpose

* `curryQ : (A ⊗ₙ B ⟶ C) → (A ⟶ B ⊸ₛ C)`.

`curryQ g a` is a class `⟦f_a⟧` of a *total* finitely-supported `f_a : B.obj.V → C.obj.V` whose
restriction to the fresh locus `{b | Separated a b}` is `b ↦ g ⟨(a, b), _⟩`.  Its separated values
are supported by `supp a` (`curry_sep_transport`); the further ingredient is the
**finitely-supported totalization**: extending those fresh values to a total function with finite
support (the classical fresh/`some`-`any` extension; `f_a` supported by `supp a` after a default is
chosen off the fresh locus).  This totalization is a *section* of the quotient map.  With `curryQ`
in hand:

* `uncurryQ (curryQ g) = g` is immediate on separated pairs (β for `uncurryQ`);
* `curryQ (uncurryQ h) = h` follows from `uncurryQ_injective` together with the β-rule;
* the adjunction naturality and triangle identities are then routine, giving `Closed B` for every
  `B` and `MonoidalClosed Nom`.

The reusable nominal core of the totalization — least-support equivariance (`supp_smul`), the fresh
renaming (`exists_avoiding_perm`), and the fresh-representative machinery (`exists_fresh_rep`,
`evalCls`, `evalCls_eq`) — is provided above. -/

end Nominal
