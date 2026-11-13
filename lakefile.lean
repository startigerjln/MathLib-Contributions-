import Lake
open Lake DSL

package «MathLibContributions» where
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLinkArgs := #["-L./.lake/packages/mathlib/.lake/build/lib", "-lMathlib"]

@[default_target]
lean_lib «Contributions» where
  srcDir := "Contributions"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.16.0-rc1"
