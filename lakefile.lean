import Lake
open Lake DSL

package «maths» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "db127794c79fdeb86f6b0cf6ff2c804026fbaff1"

require «PrimeNumberTheoremAnd» from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @
    "6739793850d3eaa031e3543ed72d7f026f8080f5"

@[default_target]
lean_lib RiemannHypothesisProject where
