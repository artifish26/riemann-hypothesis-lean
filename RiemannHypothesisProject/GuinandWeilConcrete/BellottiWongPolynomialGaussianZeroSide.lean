import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianZeroSide
import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongCutoffThreeCount

/-!
# Bellotti-Wong polynomial-Gaussian zero-side summability

This is the narrow analytic endpoint of the p-series track.  The exact
published Bellotti-Wong `N(T)` theorem gives the cutoff-three quadratic count,
while fourth-order bounded-strip decay of the concrete polynomial-Gaussian
source supplies the summable weight.  No explicit-formula identity is used.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

namespace BellottiWongPublishedExactNTTheorem

/-- The exact Bellotti-Wong `N(T)` theorem implies absolute convergence of
the actual completed-zeta polynomial-Gaussian zero weight. -/
theorem summable_norm_polynomialGaussianCompletedZetaZeroWeight
    (source : BellottiWongPublishedExactNTTheorem)
    (p : Polynomial Complex) :
    Summable
      (fun rho : ZetaZeroSubtype =>
        norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) := by
  apply
    summable_norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_of_one_le_cutoff
      p source.toPolynomialZeroCountingEstimateCutoffThree (k := 4)
  · rw [source.toPolynomialZeroCountingEstimateCutoffThree_cutoff]
    norm_num
  · rw [source.toPolynomialZeroCountingEstimateCutoffThree_growth]
    norm_num

/-- Signed convergence of the actual completed-zeta polynomial-Gaussian zero
weight follows from the absolute-convergence theorem. -/
theorem summable_polynomialGaussianCompletedZetaZeroWeight
    (source : BellottiWongPublishedExactNTTheorem)
    (p : Polynomial Complex) :
    Summable (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p) :=
  (source.summable_norm_polynomialGaussianCompletedZetaZeroWeight p).of_norm

end BellottiWongPublishedExactNTTheorem

end


end ComplexCompactExhaustion

end RiemannHypothesisProject
