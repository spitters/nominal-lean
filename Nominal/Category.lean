/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Category.Nominal
import Nominal.Category.NominalMonoidal
import Nominal.Category.NominalMonoidalClosed
import Nominal.Category.NominalMonoidalClosedFull
import Nominal.Category.NominalMonoidalClosedComplete
import Nominal.Category.NominalSeparatedExp

/-!
# The category of nominal sets

The categorical (Schanuel-topos) layer over the core nominal-sets development:
the category of nominal sets, its symmetric-monoidal and monoidal-closed
structure, and the internal separated exponential. Depends only on mathlib and
`Nominal.*`.

## Not yet re-imported: the name-abstraction / core-equivalence subtree

`NominalAbstraction`, `NominalCoreBridge`, `NominalCoreEquivalence`,
`NominalCoreEquivalenceComplete`, `NominalAbstractionClosed`,
`NominalAbstractionAdjunction`, `NominalAbstractionNatIso`, and
`NominalAbstractionRecursion` are present in this directory but not imported
here: they carry pre-existing rot from the Lean 4.30 `Action` API change. The
`End`-valued action `X.ρ π : End X.V` is no longer a bare function; the current
idiom is `GSet.act π x = ConcreteCategory.hom (X.ρ π) x` (see `Category/Nominal.lean`).
`NominalAbstraction` and `NominalCoreBridge` still apply the old `X.ρ π x` form
and fail to elaborate; the other six depend on them transitively. This rot
predates the split — the same files fail to build in their original
`CatCrypt/Category/` location — and was invisible there because nothing in the
main `CatCrypt.Crypto` build imports them. Repairing the two roots (rewrite bare
`X.ρ · ·` to `GSet.act · ·`) unblocks the subtree.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*,
  Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/
