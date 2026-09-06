/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Nominal.Category.NominalAbstraction
public import Nominal.Category.NominalCoreEquivalence
public import Nominal.Category.NominalCoreEquivalenceComplete

set_option autoImplicit false

/-!
# Atom abstraction commutes with the Schanuel equivalence, as a natural isomorphism

`CatCrypt.Category.NominalAbstraction` builds atom abstraction as an endofunctor `absF : Nom ⥤ Nom`
on the full-permutation side. `CatCrypt.Category.NominalCoreEquivalence` builds the restriction
functor `res : Nom ⥤ NomFin` to the finitely-supported-permutation side (the Schanuel
identification, completed to an equivalence in `NominalCoreEquivalenceComplete`).

This file promotes the object-level fact "abstraction is the same construction on both sides" to a
genuine **natural isomorphism of functors** over the category `NomFin`. It supplies:

1. `absFinF : NomFin ⥤ NomFin` — the native atom-abstraction endofunctor on `NomFin`, the `FinPerm`
   copy of `absF`. It mirrors `absObj`/`absF` verbatim over the finitely-supported permutation
   group: `absGSetFin X = (Atom × X.V)/AbsRelFin` with the diagonal `FinPerm`-action, the same
   cofinite α-equivalence, and the same support-shrink argument (`s \ {a}` supports the class of
   `(a, x)`). `map_id`/`map_comp` are proved.

2. `absIntertwine : res ⋙ absFinF ≅ absF ⋙ res` — the **intertwining natural isomorphism**. Its
   component at `X` identifies `absFinObj (res.obj X)` with `res.obj (absObj X)`: both are the same
   α-equivalence quotient of `Atom × X.V`, because `res` only restricts the action along
   `finPermToPerm` and every swap used in the α-equivalence lives in `FinPerm` already (a `FinPerm`
   swap acts identically whether viewed in `FinPerm` or pushed to the full group via
   `finPermToPerm` — `finPermToPerm_swap`). The component bijection reindexes the atom coordinate
   along `coreAtomEquiv`; equivariance and naturality both reduce to `Quotient.inductionOn` plus
   that swap-transport identity.

3. `absPreservedBySchanuel : absF ⋙ res ≅ res ⋙ absFinF` — the headline restatement:
   atom abstraction is preserved by the Schanuel equivalence.

## Relation to the data-class abstraction

The *object-level* tie of categorical abstraction to SSProve's data-class `NameAbs` is
`NominalAbstractionRecursion.coreAbsIso`. This file supplies the complementary *functorial*
statement: abstraction, as a functor, commutes (up to natural isomorphism) with the restriction
functor `res` witnessing the Schanuel equivalence `NomFin ≌ Nom`. This is exactly the form the
identification would take through a bundled core category — `NomFin` is that bundled category, and
`absIntertwine` is the natural isomorphism the object-level statement was a shadow of.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

@[expose] public section

open CategoryTheory

namespace Nominal

open CatCrypt.Nominal

/-! ## Part 1 — native atom abstraction `absFinF : NomFin ⥤ NomFin` -/

/-- Conjugation of a `FinPerm` transposition through a `FinPerm`:
`FinPerm.swap (π a) (π b) * π = π * FinPerm.swap a b`. The `FinPerm` mirror of
`Nominal.swap_mul_perm`. -/
lemma swapFin_mul_perm (π : FinPerm) (a b : CatCrypt.Nominal.Atom) :
    FinPerm.swap (π a) (π b) * π = π * FinPerm.swap a b := by
  ext d
  simp only [FinPerm.mul_apply]
  by_cases hda : d = a
  · subst hda; simp only [FinPerm.swap_apply_left]
  · by_cases hdb : d = b
    · subst hdb; simp only [FinPerm.swap_apply_right]
    · rw [FinPerm.swap_apply_of_ne_of_ne hda hdb,
          FinPerm.swap_apply_of_ne_of_ne
            (fun h => hda (π.val.injective (by simpa using h)))
            (fun h => hdb (π.val.injective (by simpa using h)))]

/-- α-equivalence on representatives `Atom × X.V` for a `FinPerm`-set, cofinite form: the swapped
representatives agree at every atom outside some finite set. The `FinPerm` mirror of `AbsRel`. -/
def AbsRelFin (X : GSetFin) (p q : CatCrypt.Nominal.Atom × X.V) : Prop :=
  ∃ s : Finset CatCrypt.Nominal.Atom,
    ∀ c ∉ s, X.act (FinPerm.swap p.1 c) p.2 = X.act (FinPerm.swap q.1 c) q.2

namespace AbsRelFin

variable {X : GSetFin}

/-- Reflexivity. -/
theorem refl (p : CatCrypt.Nominal.Atom × X.V) : AbsRelFin X p p := ⟨∅, fun _ _ => rfl⟩

/-- Symmetry. -/
theorem symm {p q : CatCrypt.Nominal.Atom × X.V} (h : AbsRelFin X p q) : AbsRelFin X q p :=
  h.imp fun _ hs c hc => (hs c hc).symm

/-- Transitivity. -/
theorem trans {p q r : CatCrypt.Nominal.Atom × X.V}
    (hpq : AbsRelFin X p q) (hqr : AbsRelFin X q r) : AbsRelFin X p r := by
  obtain ⟨s₁, h₁⟩ := hpq
  obtain ⟨s₂, h₂⟩ := hqr
  refine ⟨s₁ ∪ s₂, fun c hc => ?_⟩
  rw [Finset.mem_union, not_or] at hc
  exact (h₁ c hc.1).trans (h₂ c hc.2)

end AbsRelFin

/-- The setoid for atom abstraction on the `FinPerm` side. -/
def absSetoidFin (X : GSetFin) : Setoid (CatCrypt.Nominal.Atom × X.V) where
  r := AbsRelFin X
  iseqv := ⟨AbsRelFin.refl, AbsRelFin.symm, AbsRelFin.trans⟩

/-- α-equivalence is preserved by the diagonal `FinPerm`-action. -/
theorem AbsRelFin_smul {X : GSetFin} (π : FinPerm) {p q : CatCrypt.Nominal.Atom × X.V}
    (h : AbsRelFin X p q) :
    AbsRelFin X (π p.1, X.act π p.2) (π q.1, X.act π q.2) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s.image (π ·), fun d hd => ?_⟩
  have hdc : π (π⁻¹ d) = d := by
    rw [← FinPerm.mul_apply, mul_inv_cancel, FinPerm.one_apply]
  have hc : π⁻¹ d ∉ s := by
    intro hmem
    exact hd (by simpa [hdc] using Finset.mem_image_of_mem (π ·) hmem)
  have hkey := hs (π⁻¹ d) hc
  calc X.act (FinPerm.swap (π p.1) d) (X.act π p.2)
      = X.act (FinPerm.swap (π p.1) (π (π⁻¹ d)) * π) p.2 := by
        rw [hdc, ← GSetFin.act_mul]
    _ = X.act (π * FinPerm.swap p.1 (π⁻¹ d)) p.2 := by rw [swapFin_mul_perm]
    _ = X.act π (X.act (FinPerm.swap p.1 (π⁻¹ d)) p.2) := GSetFin.act_mul X _ _ _
    _ = X.act π (X.act (FinPerm.swap q.1 (π⁻¹ d)) q.2) := by rw [hkey]
    _ = X.act (π * FinPerm.swap q.1 (π⁻¹ d)) q.2 := (GSetFin.act_mul X _ _ _).symm
    _ = X.act (FinPerm.swap (π q.1) (π (π⁻¹ d)) * π) q.2 := by rw [swapFin_mul_perm]
    _ = X.act (FinPerm.swap (π q.1) d) (X.act π q.2) := by rw [hdc, ← GSetFin.act_mul]

/-- The underlying `GSetFin` of `[𝔸]X` on the `FinPerm` side: the quotient of `Atom × X.V` by
α-equivalence, with the diagonal action `π • ⟦(a, x)⟧ = ⟦(π a, X.act π x)⟧`. -/
def absGSetFin (X : GSetFin) : GSetFin where
  V := Quotient (absSetoidFin X)
  ρ :=
    { toFun := fun π => TypeCat.ofHom
        (Quotient.map (fun p => (π p.1, X.act π p.2)) (fun _ _ h => AbsRelFin_smul π h))
      map_one' := by
        apply ConcreteCategory.hom_ext; intro q
        induction q using Quotient.inductionOn with
        | _ p =>
          show Quotient.mk (absSetoidFin X) ((1 : FinPerm) p.1, X.act (1 : FinPerm) p.2)
            = Quotient.mk (absSetoidFin X) p
          rw [FinPerm.one_apply, GSetFin.act_one]
      map_mul' := fun a b => by
        apply ConcreteCategory.hom_ext; intro q
        induction q using Quotient.inductionOn with
        | _ p =>
          show Quotient.mk (absSetoidFin X) ((a * b) p.1, X.act (a * b) p.2)
            = Quotient.mk (absSetoidFin X) (a (b p.1), X.act a (X.act b p.2))
          rw [GSetFin.act_mul]; rfl }

/-- Abstraction point on the `FinPerm` side: the class of `(a, x)` in `[𝔸]X`. -/
def absPtFin (X : GSetFin) (a : CatCrypt.Nominal.Atom) (x : X.V) : (absGSetFin X).V :=
  Quotient.mk (absSetoidFin X) (a, x)

/-- **Support-shrink** (`FinPerm` side): if `s` supports `x`, then `s \ {a}` supports the class of
`(a, x)`. The mirror of `absGSet_supports`. -/
theorem absGSetFin_supports {X : GSetFin} {s : Finset CatCrypt.Nominal.Atom}
    {a : CatCrypt.Nominal.Atom} {x : X.V} (hs : SupportsFin X s x) :
    SupportsFin (absGSetFin X) (s \ {a}) (absPtFin X a x) := by
  intro π hπ
  show Quotient.mk (absSetoidFin X) (π a, X.act π x) = Quotient.mk (absSetoidFin X) (a, x)
  apply Quotient.sound
  refine ⟨insert a (insert (π a) s), fun c hc => ?_⟩
  simp only [Finset.mem_insert, not_or] at hc
  obtain ⟨hca, hcπa, hcs⟩ := hc
  show X.act (FinPerm.swap (π a) c) (X.act π x) = X.act (FinPerm.swap a c) x
  rw [← GSetFin.act_mul]
  apply actFin_eq_of_agree hs
  intro d hd
  rw [FinPerm.mul_apply]
  by_cases hda : d = a
  · subst hda
    rw [FinPerm.swap_apply_left, FinPerm.swap_apply_left]
  · have hπd : π d = d := hπ d (Finset.mem_sdiff.mpr ⟨hd, Finset.notMem_singleton.mpr hda⟩)
    have hdc : d ≠ c := fun h => hcs (h ▸ hd)
    have hdπa : d ≠ π a := by
      intro h
      exact hda (π.val.injective (hπd.trans h))
    rw [hπd, FinPerm.swap_apply_of_ne_of_ne hdπa hdc, FinPerm.swap_apply_of_ne_of_ne hda hdc]

/-- `[𝔸]X` is nominal on the `FinPerm` side: every class has finite support (`supp x \ {a}`). -/
theorem absGSetFin_isNominalFin {X : GSetFin} (hX : IsNominalFin X) :
    IsNominalFin (absGSetFin X) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    obtain ⟨s, hs⟩ := hX p.2
    exact ⟨s \ {p.1}, absGSetFin_supports hs⟩

/-- Atom abstraction `[𝔸]X` on objects of `NomFin`. -/
def absObjFin (X : NomFin) : NomFin :=
  NomFin.of (absGSetFin X.obj) (absGSetFin_isNominalFin X.property)

/-- α-equivalence is transported along a `FinPerm`-equivariant map (used for the map on
morphisms). The mirror of `AbsRel_map`. -/
theorem AbsRelFin_map {X Y : GSetFin} (f : X ⟶ Y) {p q : CatCrypt.Nominal.Atom × X.V}
    (h : AbsRelFin X p q) : AbsRelFin Y (p.1, f.hom p.2) (q.1, f.hom q.2) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun c hc => ?_⟩
  have e := hs c hc
  have fp : f.hom (X.act (FinPerm.swap p.1 c) p.2) = Y.act (FinPerm.swap p.1 c) (f.hom p.2) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (f.comm (FinPerm.swap p.1 c)) p.2
  have fq : f.hom (X.act (FinPerm.swap q.1 c) q.2) = Y.act (FinPerm.swap q.1 c) (f.hom q.2) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (f.comm (FinPerm.swap q.1 c)) q.2
  rw [← fp, ← fq, e]

/-- The action of atom abstraction on a morphism `f : X ⟶ Y` of `GSetFin`s. -/
def absHomFin {X Y : GSetFin} (f : X ⟶ Y) : absGSetFin X ⟶ absGSetFin Y where
  hom := TypeCat.ofHom (Quotient.map (fun p => (p.1, f.hom p.2)) (fun _ _ h => AbsRelFin_map f h))
  comm := by
    intro π
    apply ConcreteCategory.hom_ext; intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      show Quotient.mk (absSetoidFin Y) (π p.1, f.hom (X.act π p.2))
        = Quotient.mk (absSetoidFin Y) (π p.1, Y.act π (f.hom p.2))
      have hc : f.hom (X.act π p.2) = Y.act π (f.hom p.2) := by
        simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (f.comm π) p.2
      rw [hc]

/-- Atom abstraction as an endofunctor on `NomFin`. The `FinPerm` copy of `absF`. -/
def absFinF : NomFin ⥤ NomFin where
  obj X := absObjFin X
  map {X Y} f := ⟨absHomFin f.hom⟩
  map_id X := by
    apply InducedCategory.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext; intro q
    induction q using Quotient.inductionOn with
    | _ p => rfl
  map_comp {X Y Z} f g := by
    apply InducedCategory.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext; intro q
    induction q using Quotient.inductionOn with
    | _ p => rfl

/-! ## Part 2 — the intertwining natural isomorphism `res ⋙ absFinF ≅ absF ⋙ res` -/

/-- A `FinPerm` transposition, pushed to the full permutation group via `finPermToPerm`, is the
full-group transposition of the transported atoms. This is why the α-equivalence agrees on both
sides. -/
lemma finPermToPerm_swap (a c : CatCrypt.Nominal.Atom) :
    finPermToPerm (FinPerm.swap a c) = Equiv.swap (coreAtomEquiv a) (coreAtomEquiv c) := by
  ext d
  simp only [finPermToPerm, MonoidHom.coe_mk, OneHom.coe_mk, FinPerm.swap_val,
    Equiv.permCongr_apply]
  by_cases hda : d = coreAtomEquiv a
  · subst hda
    rw [Equiv.symm_apply_apply, Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hdc : d = coreAtomEquiv c
    · subst hdc
      rw [Equiv.symm_apply_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
    · have h1 : coreAtomEquiv.symm d ≠ a := by
        intro h; exact hda (by rw [← h, Equiv.apply_symm_apply])
      have h2 : coreAtomEquiv.symm d ≠ c := by
        intro h; exact hdc (by rw [← h, Equiv.apply_symm_apply])
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.apply_symm_apply,
          Equiv.swap_apply_of_ne_of_ne hda hdc]

/-- Reindexing (forward): the `FinPerm`-side α-equivalence of the restricted action pushes to the
full-side α-equivalence, along `coreAtomEquiv` on the atom coordinate. -/
theorem absRelFin_res_of {X : GSet} {p q : CatCrypt.Nominal.Atom × X.V}
    (h : AbsRelFin (resGSet.obj X) p q) :
    AbsRel X (coreAtomEquiv p.1, p.2) (coreAtomEquiv q.1, q.2) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s.image coreAtomEquiv, fun d hd => ?_⟩
  have hpre : coreAtomEquiv.symm d ∉ s := by
    intro hmem
    exact hd (by simpa using Finset.mem_image_of_mem coreAtomEquiv hmem)
  have hkey := hs (coreAtomEquiv.symm d) hpre
  have e1 : Equiv.swap (coreAtomEquiv p.1) d
      = finPermToPerm (FinPerm.swap p.1 (coreAtomEquiv.symm d)) := by
    rw [finPermToPerm_swap, Equiv.apply_symm_apply]
  have e2 : Equiv.swap (coreAtomEquiv q.1) d
      = finPermToPerm (FinPerm.swap q.1 (coreAtomEquiv.symm d)) := by
    rw [finPermToPerm_swap, Equiv.apply_symm_apply]
  show X.act (Equiv.swap (coreAtomEquiv p.1) d) p.2 = X.act (Equiv.swap (coreAtomEquiv q.1) d) q.2
  rw [e1, e2]
  exact hkey

/-- Reindexing (backward): the full-side α-equivalence pulls back to the `FinPerm`-side
α-equivalence of the restricted action, along `coreAtomEquiv.symm` on the atom coordinate. -/
theorem absRelFin_res_symm {X : GSet} {p q : Nominal.Atom × X.V} (h : AbsRel X p q) :
    AbsRelFin (resGSet.obj X) (coreAtomEquiv.symm p.1, p.2) (coreAtomEquiv.symm q.1, q.2) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s.image coreAtomEquiv.symm, fun c' hc' => ?_⟩
  have hpre : coreAtomEquiv c' ∉ s := by
    intro hmem
    exact hc' (by simpa using Finset.mem_image_of_mem coreAtomEquiv.symm hmem)
  have hkey := hs (coreAtomEquiv c') hpre
  show X.act (finPermToPerm (FinPerm.swap (coreAtomEquiv.symm p.1) c')) p.2
     = X.act (finPermToPerm (FinPerm.swap (coreAtomEquiv.symm q.1) c')) q.2
  rw [finPermToPerm_swap, finPermToPerm_swap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hkey

/-- The underlying carrier bijection of the intertwining component: the two α-equivalence quotients
of `res.obj X` and `absObj X` are the same, reindexed along `coreAtomEquiv` on the atom
coordinate. -/
noncomputable def absIntertwineEquiv (X : GSet) :
    (absGSetFin (resGSet.obj X)).V ≃ (resGSet.obj (absGSet X)).V where
  toFun := Quotient.map (fun p => (coreAtomEquiv p.1, p.2)) (fun _ _ h => absRelFin_res_of h)
  invFun := Quotient.map (fun p => (coreAtomEquiv.symm p.1, p.2))
    (fun _ _ h => absRelFin_res_symm h)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      obtain ⟨a, x⟩ := p
      show Quotient.mk (absSetoidFin (resGSet.obj X)) (coreAtomEquiv.symm (coreAtomEquiv a), x)
        = Quotient.mk (absSetoidFin (resGSet.obj X)) (a, x)
      rw [Equiv.symm_apply_apply]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      obtain ⟨a, x⟩ := p
      show Quotient.mk (absSetoid X) (coreAtomEquiv (coreAtomEquiv.symm a), x)
        = Quotient.mk (absSetoid X) (a, x)
      rw [Equiv.apply_symm_apply]

/-- The intertwining component as an iso of `GSetFin` objects:
`absGSetFin (res.obj X) ≅ res.obj (absObj X)`, equivariant for the `FinPerm`-action. -/
noncomputable def absIntertwineGSetIso (X : Nom) :
    (absFinF.obj (res.obj X)).obj ≅ (res.obj (absF.obj X)).obj :=
  Action.mkIso (Equiv.toIso (absIntertwineEquiv X.obj))
    (by
      intro τ
      apply ConcreteCategory.hom_ext; intro q
      induction q using Quotient.inductionOn with
      | _ p =>
        obtain ⟨a, x⟩ := p
        show Quotient.mk (absSetoid X.obj)
              (coreAtomEquiv (τ a), X.obj.act (finPermToPerm τ) x)
            = Quotient.mk (absSetoid X.obj)
              (finPermToPerm τ (coreAtomEquiv a), X.obj.act (finPermToPerm τ) x)
        have hkey : coreAtomEquiv (τ a) = finPermToPerm τ (coreAtomEquiv a) := by
          simp [finPermToPerm, coreAtomEquiv, Equiv.permCongr_apply]
        rw [hkey])

/-- The intertwining component as an iso of `NomFin` objects. -/
noncomputable def absIntertwineIso (X : Nom) :
    (res ⋙ absFinF).obj X ≅ (absF ⋙ res).obj X :=
  ObjectProperty.isoMk _ (absIntertwineGSetIso X)

/-- **The intertwining natural isomorphism.** `res` carries categorical atom abstraction to the
native `NomFin`-abstraction, naturally: `res ⋙ absFinF ≅ absF ⋙ res`. Componentwise both
functors are the same α-equivalence quotient of `Atom × X.V`; naturality holds because both legs
send `⟦(a, x)⟧` to `⟦(coreAtomEquiv a, f x)⟧`. -/
noncomputable def absIntertwine : res ⋙ absFinF ≅ absF ⋙ res :=
  NatIso.ofComponents absIntertwineIso
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply ConcreteCategory.hom_ext; intro q
      induction q using Quotient.inductionOn with
      | _ p => rfl)

/-! ## Part 3 — the Schanuel-preservation restatement -/

/-- **Atom abstraction is preserved by the Schanuel equivalence.** The restatement of
`absIntertwine`: `absF ⋙ res ≅ res ⋙ absFinF`. -/
noncomputable def absPreservedBySchanuel : absF ⋙ res ≅ res ⋙ absFinF := absIntertwine.symm

end Nominal
