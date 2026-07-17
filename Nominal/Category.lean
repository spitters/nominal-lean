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
import Nominal.Category.NominalAbstraction
import Nominal.Category.NominalCoreBridge
import Nominal.Category.NominalCoreEquivalence
import Nominal.Category.NominalCoreEquivalenceComplete
import Nominal.Category.NominalAbstractionClosed
import Nominal.Category.NominalAbstractionAdjunction
import Nominal.Category.NominalAbstractionNatIso
import Nominal.Category.NominalAbstractionRecursion

/-!
# The category of nominal sets

The categorical (Schanuel-topos) layer over the core nominal-sets development:
the category of nominal sets, its symmetric-monoidal and monoidal-closed
structure, the internal separated exponential, atom abstraction `[𝔸](−)` with its
binding adjunction and recursion principle, and the equivalence with the core
finitely-supported `FinPerm`-sets. Depends only on mathlib and `Nominal.*`.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*,
  Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/
