import Lake
open Lake DSL

package nominalLean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Nominal where
  -- Module root `Nominal.*`. The pure nominal-sets development (Gabbay–Pitts):
  -- names, finite permutations, nominal sets, freshness, support, name
  -- abstraction, and the categorical (Schanuel-topos) layer. Depends only on
  -- mathlib. Declared namespaces remain `CatCrypt.Nominal` / `CatCrypt.Category`
  -- so downstream `CatCryptCore` / `CatCrypt` shims re-export without churn.
  globs := #[.andSubmodules `Nominal]

-- Module root `NominalIris.*` (namespace `Nominal.Iris`). The Iris/BI reading of
-- nominal separation: disjoint name-support as a model of bunched implications,
-- its `DisjointLeibnizSet` camera, and the `iOwn` name-allocation view-shift.
-- A separate library so the core `Nominal` target stays mathlib-only; only this
-- target pulls in iris-lean.
lean_lib NominalIris where
  globs := #[.andSubmodules `NominalIris]

-- mathlib: the core dependency.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

-- iris-lean (Lean 4 Iris port): BI + proof mode + cameras + the IProp base logic.
-- Used only by the `NominalIris` target.
require iris from git
  "https://github.com/leanprover-community/iris-lean" @ "v4.30.0" / "Iris"
