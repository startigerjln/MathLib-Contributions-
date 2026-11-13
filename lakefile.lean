import Lake
open Lake DSL

package «MathLibContributions» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «MathLibContributions» where
  roots := #[`Contributions]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.16.0-rc1"
