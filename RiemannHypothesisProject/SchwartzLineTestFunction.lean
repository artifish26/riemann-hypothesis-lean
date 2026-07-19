import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz line test functions

This foundation module fixes the common test-function type without importing
any explicit-formula or positivity endpoint.
-/

namespace RiemannHypothesisProject

/-- The project's Schwartz test-function class on the real line. -/
abbrev SchwartzLineTestFunction := SchwartzMap Real Complex

end RiemannHypothesisProject
