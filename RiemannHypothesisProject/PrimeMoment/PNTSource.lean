import PrimeNumberTheoremAnd.MediumPNT

/-!
# Prime-number-theorem source for the Li prime moments

This module freezes the external source theorem used by the prime-moment
lane.  Project-specific cutoff normalization belongs in the next bridge layer.
-/

namespace RiemannHypothesisProject

noncomputable section

open Filter
open scoped Chebyshev

/-- The pinned `PrimeNumberTheoremAnd` medium PNT, restated with an explicit
function rather than pointwise subtraction notation. -/
theorem mediumPNT_remainder :
    ∃ c > 0,
      (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
        fun x : ℝ =>
          x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, hPNT⟩ := MediumPNT
  refine ⟨c, hc, ?_⟩
  have hfun : Chebyshev.psi - id =
      fun x : ℝ => Chebyshev.psi x - x := by
    rfl
  rw [← hfun]
  exact hPNT

end

end RiemannHypothesisProject
