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

-- mathlib only: this is an upstream leaf. No crypto / SSProve-package deps.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"
