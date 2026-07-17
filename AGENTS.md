# AGENTS.md — nominal-lean

## Role in the workspace

This is the **upstream source** and maintained home of the Gabbay–Pitts
nominal-sets development. Edit the nominal theory **here**.

These are **shims** that re-export this library — do not add or edit nominal
content in them:

- `CatCryptCore.Nominal.*` in *CatCrypt-core*
- `CatCrypt.Category.Nominal*` in the *CatCrypt* (SSProve-lean) development tree

## Module structure

Modules live under the `Nominal.*` root (`import Nominal`, `import Nominal.Category`),
so the library coexists with any package that carries its own `CatCrypt.*` module
tree. Declared namespaces are `CatCrypt.Nominal` and `CatCrypt.Category`, so the
downstream shims re-export without renaming.

## Dependency & build

Mathlib-only upstream leaf. Standalone: `lake exe cache get && lake build`. In the
connected local workspace the dependency packages are symlinked under
`.lake/packages` to the shared built mathlib tree, and CatCrypt-core / the dev
tree `require` this package by local path (a git require on publication).
