/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Nominal.Category.Nominal
public import Nominal.Category.NominalMonoidal
public import Nominal.Category.NominalMonoidalClosed
public import Nominal.Category.NominalMonoidalClosedFull
public import Nominal.Category.NominalMonoidalClosedComplete
public import Nominal.Category.NominalSeparatedExp
public import Nominal.Category.NominalAbstraction
public import Nominal.Category.NominalCoreBridge
public import Nominal.Category.NominalCoreEquivalence
public import Nominal.Category.NominalCoreEquivalenceComplete
public import Nominal.Category.NominalAbstractionClosed
public import Nominal.Category.NominalAbstractionAdjunction
public import Nominal.Category.NominalAbstractionNatIso
public import Nominal.Category.NominalAbstractionRecursion

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
