/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/
import Iris.Algebra.LeibnizSet
import Iris.Algebra.Auth
import Iris.Instances.IProp
import Nominal.Atom

set_option autoImplicit false

/-!
# The name camera and `iOwn` ghost state, over nominal `Atom`

The `DisjointLeibnizSet` name camera and its `Auth` / `iOwn` ghost-state layer,
over nominal-lean's `Atom` (so it shares the `Atom`/`FinPerm`/`NomSet` framework
with the nominal λ-terms). This is the atom-agnostic part of the camera
development — no concrete `HeapProp` BI is needed for the ghost-state name
allocator (the `den` bridge to the concrete BI lives in `NominalIris.Den`).

* `NameRA` — the name camera (`DisjointLeibnizSet` over finite atom sets).
* `name_alloc` — the `Auth` allocation view-shift `● S ~~> ● (S ∪ {a}) • ◯ {a}`.
* `ownAuth` / `ownFresh` — `iOwn` ghost ownership; `own_name_alloc`,
  `own_name_alloc_init`, `ownFresh_distinct`; `HasNameAlloc` + points-to notation.
-/

namespace NominalIris

open CatCrypt.Nominal (Atom)
open Iris Iris.BI CMRA

/-! ## Finite atom sets as an iris-lean lawful set -/

/-- Finite atom sets, the carrier of the name camera. -/
structure NameSet where
  ofFinset ::
  toFinset : Finset Atom
deriving DecidableEq

namespace NameSet

instance : Membership Atom NameSet := ⟨fun s a => a ∈ s.toFinset⟩
instance : Singleton Atom NameSet := ⟨fun a => ⟨{a}⟩⟩
instance : Union NameSet := ⟨fun s t => ⟨s.toFinset ∪ t.toFinset⟩⟩
instance : Inter NameSet := ⟨fun s t => ⟨s.toFinset ∩ t.toFinset⟩⟩
instance : SDiff NameSet := ⟨fun s t => ⟨s.toFinset \ t.toFinset⟩⟩
instance : EmptyCollection NameSet := ⟨⟨∅⟩⟩

@[simp] theorem mem_iff (a : Atom) (s : NameSet) : a ∈ s ↔ a ∈ s.toFinset := Iff.rfl
@[simp] theorem toFinset_singleton (a : Atom) : ({a} : NameSet).toFinset = {a} := rfl
@[simp] theorem toFinset_union (s t : NameSet) :
    (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := rfl
@[simp] theorem toFinset_inter (s t : NameSet) :
    (s ∩ t).toFinset = s.toFinset ∩ t.toFinset := rfl
@[simp] theorem toFinset_sdiff (s t : NameSet) :
    (s \ t).toFinset = s.toFinset \ t.toFinset := rfl
@[simp] theorem toFinset_empty : (∅ : NameSet).toFinset = ∅ := rfl

instance : Iris.Std.Set NameSet Atom where

instance : Iris.Std.LawfulSet NameSet Atom where
  ext {X Y} h := by cases X; cases Y; congr 1; exact Finset.ext h
  mem_empty {x} := by simp
  mem_singleton {x y} := by simp [Finset.mem_singleton]
  mem_union {X Y x} := by simp [Finset.mem_union]
  mem_inter {X Y x} := by simp [Finset.mem_inter]
  mem_diff {X Y x} := by simp [Finset.mem_sdiff]

/-- iris-lean `##` on `NameSet` is mathlib `Finset` disjointness of the carriers. -/
theorem disjoint_iff (s t : NameSet) : s ## t ↔ Disjoint s.toFinset t.toFinset := by
  rw [Finset.disjoint_left]
  exact ⟨fun h a ha hb => h a ⟨ha, hb⟩, fun h a hab => h hab.1 hab.2⟩

theorem union_comm (s t : NameSet) : s ∪ t = t ∪ s := by
  cases s; cases t
  show NameSet.ofFinset _ = NameSet.ofFinset _
  rw [Finset.union_comm]

end NameSet

/-! ## The name camera -/

open DisjointLeibnizSet

/-- The **name camera**: finite atom sets under disjoint union, a `UCMRA`. -/
abbrev NameRA : Type := DisjointLeibnizSet NameSet

/-- The **fresh-name resource** as a camera fragment: the world holding exactly `a`. -/
def freshRA (a : Atom) : NameRA := .valid {a}

theorem op_valid_valid (a b : NameSet) :
    (DisjointLeibnizSet.valid a) • (DisjointLeibnizSet.valid b)
      = if a ## b then .valid (a ∪ b) else .error := rfl

theorem op_error_left (y : NameRA) : (DisjointLeibnizSet.error) • y = .error := rfl

theorem op_valid_error (a : NameSet) :
    (DisjointLeibnizSet.valid a) • (DisjointLeibnizSet.error) = .error := rfl

/-- Camera validity of the combined fragments encodes distinctness of the names. -/
theorem freshRA_valid_op_iff (a b : Atom) : ✓ (freshRA a • freshRA b) ↔ a ≠ b := by
  rw [freshRA, freshRA, valid_op_iff_disj, NameSet.disjoint_iff,
    NameSet.toFinset_singleton, NameSet.toFinset_singleton, Finset.disjoint_singleton]

/-! ## `Auth` allocation -/

section Allocation

open OFE

variable {F : Type _} [UFraction F]

/-- The **allocation local update**: an unused name `a` may be split off the
empty fragment, growing the authority from `S` to `S ∪ {a}`. -/
theorem alloc_localUpdate {S : NameSet} {a : Atom} (h : a ∉ S) :
    ((DisjointLeibnizSet.valid S, (UCMRA.unit : NameRA)) : NameRA × NameRA) ~l~>
      (DisjointLeibnizSet.valid (S ∪ {a}), DisjointLeibnizSet.valid {a}) := by
  rw [local_update_unital_discrete]
  intro z _ he
  have hz : (DisjointLeibnizSet.valid S) = z :=
    Leibniz.leibniz.mp (he.trans (UCMRA.unit_left_id (x := z)))
  subst hz
  refine ⟨trivial, ?_⟩
  have hdisj : ({a} : NameSet) ## S := by
    rw [NameSet.disjoint_iff, NameSet.toFinset_singleton, Finset.disjoint_singleton_left]
    exact h
  calc DisjointLeibnizSet.valid (S ∪ {a})
      = DisjointLeibnizSet.valid ({a} ∪ S) := by rw [NameSet.union_comm]
    _ ≡ (DisjointLeibnizSet.valid ({a} : NameSet)) • (DisjointLeibnizSet.valid S) :=
        (disj_op_union hdisj).symm

/-- **In-logic name allocation** — the frame-preserving update in `Auth F NameRA`. -/
theorem name_alloc {S : NameSet} {a : Atom} (h : a ∉ S) :
    (Auth.authFull (DisjointLeibnizSet.valid S) : Auth F NameRA) ~~>
      (Auth.authFull (DisjointLeibnizSet.valid (S ∪ {a}))) • Auth.frag (freshRA a) :=
  Auth.auth_update_alloc (alloc_localUpdate h)

/-- Validity of two combined fresh fragments encodes distinctness. -/
theorem frag_freshRA_valid_ne {a b : Atom}
    (hv : ✓ ((Auth.frag (freshRA a) • Auth.frag (freshRA b)) : Auth F NameRA)) : a ≠ b := by
  rw [← Auth.frag_op] at hv
  refine (freshRA_valid_op_iff a b).mp ?_
  rw [CMRA.valid_iff_validN]
  exact fun n => Auth.frag_validN.mp (CMRA.valid_iff_validN.mp hv n)

end Allocation

/-! ## `iOwn` ghost ownership -/

section Own

open Iris.BI COFE

variable {Fr : Type _} [UFraction Fr]
variable {GF : BundledGFunctors} [E : ElemG GF (constOF (Auth Fr NameRA))]

set_option synthInstance.maxHeartbeats 1000000 in
/-- The authoritative name camera is discrete. -/
instance nameAuth_discrete : CMRA.Discrete (Auth Fr NameRA) := inferInstance

/-- Ghost ownership of the **authoritative** allocated name-set `S` at `γ`. -/
def ownAuth (γ : GName) (S : NameSet) : IProp GF :=
  iOwn (GF := GF) (F := constOF (Auth Fr NameRA)) (E := E) γ
    (Auth.authFull (DisjointLeibnizSet.valid S))

/-- Ghost ownership of the **fresh-name fragment** for `a` at `γ`. -/
def ownFresh (γ : GName) (a : Atom) : IProp GF :=
  iOwn (GF := GF) (F := constOF (Auth Fr NameRA)) (E := E) γ (Auth.frag (freshRA a))

end Own

/-! ### Points-to notation -/

set_option synthInstance.checkSynthOrder false in
/-- `GF` carries a name allocator, recovering `GF`/`Fr` from `γ` alone. -/
class abbrev HasNameAlloc (γ : GName) (GF : outParam BundledGFunctors)
    (Fr : outParam (Type _)) [UFraction Fr] :=
  ElemG GF (constOF (Auth Fr NameRA))

/-- Owned authoritative name-set, allocator recovered from `γ`. -/
def nAuth {Fr : Type _} [UFraction Fr] {GF : BundledGFunctors} (γ : GName)
    [HasNameAlloc γ GF Fr] (S : NameSet) : IProp GF := ownAuth (Fr := Fr) γ S

/-- Owned fresh name, allocator recovered from `γ`. -/
def nFresh {Fr : Type _} [UFraction Fr] {GF : BundledGFunctors} (γ : GName)
    [HasNameAlloc γ GF Fr] (a : Atom) : IProp GF := ownFresh (Fr := Fr) γ a

@[inherit_doc] scoped notation:55 γ:56 " ⊨auth " S:56 => nAuth γ S
@[inherit_doc] scoped notation:55 γ:56 " ⊨fresh " a:56 => nFresh γ a

section Own
variable {Fr : Type _} [UFraction Fr]
variable {GF : BundledGFunctors} [E : ElemG GF (constOF (Auth Fr NameRA))]

/-- **`own`-level name allocation** (`iOwn_update ∘ name_alloc`). -/
theorem own_name_alloc (γ : GName) {S : NameSet} {a : Atom} (h : a ∉ S) :
    ownAuth (Fr := Fr) (E := E) γ S ⊢
      |==> (ownAuth (Fr := Fr) (E := E) γ (S ∪ {a}) ∗ ownFresh (Fr := Fr) (E := E) γ a) := by
  unfold ownAuth ownFresh
  exact (iOwn_update (name_alloc (F := Fr) h)).trans (BIUpdate.mono iOwn_op.1)

/-- **Creating a fresh name allocator** from nothing. -/
theorem own_name_alloc_init :
    ⊢ |==> ∃ γ, ownAuth (Fr := Fr) (E := E) γ (∅ : NameSet) := by
  unfold ownAuth
  refine iOwn_alloc _ ?_
  rw [CMRA.valid_iff_validN]
  intro n
  rw [Auth.auth_validN]
  exact trivial

/-- **Two owned fresh names are distinct** — separation forces `a ≠ b`. -/
theorem ownFresh_distinct (γ : GName) (a b : Atom) :
    (ownFresh (Fr := Fr) (E := E) γ a ∗ ownFresh (Fr := Fr) (E := E) γ b : IProp GF) ⊢
      ⌜a ≠ b⌝ := by
  unfold ownFresh
  exact iOwn_cmraValid_op.trans
    (internalCmraValid_discrete.1.trans (BI.pure_mono frag_freshRA_valid_ne))

end Own

end NominalIris
