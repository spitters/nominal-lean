/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Atom
import Nominal.FinPerm
import Nominal.Nominal
import Nominal.Fresh
import Nominal.Support
import Nominal.NameAbstraction

/-!
# Nominal sets

The Gabbay–Pitts theory of names and symmetry, over a countable set of atoms:
finite permutations, nominal sets (finitely-supported permutation actions),
freshness and the `И` (new) quantifier, support, and name abstraction. This
layer depends only on mathlib.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*,
  Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598
  — the SSProve `Nominal/` layer this development ports.
-/
