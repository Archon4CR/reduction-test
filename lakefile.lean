import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0"

require ComplexityReduction from "../ComplexityReduction"

package ReductionTest where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib ReductionTest where
