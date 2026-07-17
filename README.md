# Nominal

The Gabbay–Pitts theory of names and symmetry in Lean 4: a countable set of
atoms, finite permutations, nominal sets (finitely-supported permutation
actions), freshness and the `И` (new) quantifier, support, and name
abstraction — together with the categorical (Schanuel-topos) layer: the
category of nominal sets, its symmetric-monoidal and monoidal-closed structure,
the name-abstraction functor with its binding adjunction and recursion
principle, and the equivalence with the finitely-supported `FinPerm`-sets.

It depends only on Mathlib — no cryptography, no probability, no package algebra.

Modules live under the `Nominal.*` root (`import Nominal`, `import Nominal.Category`);
the declared namespaces are `CatCrypt.Nominal` and `CatCrypt.Category`.

## Contents

| Layer | Modules |
|---|---|
| Core (`import Nominal`) | `Atom`, `FinPerm`, `Nominal`, `Fresh`, `Support`, `NameAbstraction` — atoms, finite permutations, nominal sets, freshness/`И`, support, name abstraction |
| Category (`import Nominal.Category`) | `Category/{Nominal, NominalMonoidal, NominalMonoidalClosed, NominalMonoidalClosedFull, NominalMonoidalClosedComplete, NominalSeparatedExp}` — the category of nominal sets and its (monoidal-)closed structure |
| Category — abstraction | `Category/{NominalAbstraction, NominalAbstractionClosed, NominalAbstractionAdjunction, NominalAbstractionNatIso, NominalAbstractionRecursion}` — the atom-abstraction functor `[𝔸](−)`, its binding adjunction, and its recursion principle |
| Category — core bridge | `Category/{NominalCoreBridge, NominalCoreEquivalence, NominalCoreEquivalenceComplete}` — the equivalence between the categorical nominal sets and the core `FinPerm`-sets |

## Build

Requires [elan](https://github.com/leanprover/elan). The pinned toolchain is
`leanprover/lean4:v4.30.0` (see `lean-toolchain`).

```
lake exe cache get    # pull the Mathlib olean cache
lake build            # builds Nominal + Nominal.Category
```

## Dependencies

Pinned in `lakefile.lean` and `lake-manifest.json`:

- [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.30.0` — the only dependency.

## References

- Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge
  University Press, 2013.
- Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598
  — the SSProve `Nominal/` layer this development ports.
