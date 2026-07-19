import RiemannHypothesisProject.PrimeMoment.PNTSource
import RiemannHypothesisProject.LiCriterion.CutoffCovariance

/-!
# Chebyshev-psi normalization for the Li prime moments

The external PNT and the project cutoff use the same von Mangoldt weights.
These lemmas make the endpoint conventions and natural-number coercion exact.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open scoped ArithmeticFunction Chebyshev

/-- At a natural cutoff, Mathlib's `ψ` is exactly the project's `Icc 1 N`
von Mangoldt sum. -/
theorem chebyshevPsi_nat_eq_sum_vonMangoldt (N : ℕ) :
    Chebyshev.psi (N : ℝ) =
      ∑ m ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt m := by
  simp [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc]

/-- The unweighted summatory function underlying `liPrimeMomentCutoff` is
therefore exactly Mathlib's `Chebyshev.psi`. -/
theorem sum_vonMangoldt_eq_chebyshevPsi (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt m) =
      Chebyshev.psi (N : ℝ) :=
  (chebyshevPsi_nat_eq_sum_vonMangoldt N).symm

end


end ComplexCompactExhaustion

end RiemannHypothesisProject
