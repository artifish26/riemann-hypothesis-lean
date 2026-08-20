import Lake
open Lake DSL

package «maths» where

require «PrimeNumberTheoremAnd» from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @
    "v4.32.2"

-- Keep Mathlib last so its Lean-compatible transitive dependency pins win.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "v4.32.2"

@[default_target]
lean_lib RiemannHypothesisProject where
