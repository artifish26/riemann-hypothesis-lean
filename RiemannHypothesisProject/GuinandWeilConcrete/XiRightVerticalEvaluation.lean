import RiemannHypothesisProject.GuinandWeilConcrete.ArchimedeanGaussianBounds
import RiemannHypothesisProject.GuinandWeilConcrete.XiRightVerticalPole
import RiemannHypothesisProject.GuinandWeilConcrete.XiRightVerticalPrimeInterchange

/-!
# Complete xi right-vertical evaluation

This module assembles the independently proved rational, Archimedean, and
von Mangoldt evaluations on `re s = 5/4`.  All three complete-line integrals
are integrable, so the split below uses ordinary Bochner integral identities.
-/

namespace RiemannHypothesisProject

open Complex MeasureTheory ComplexCompactExhaustion

noncomputable section

/--
The complete right vertical integral of `xi'/xi` is exactly the checked
literature residual side, with the prime, pole, and Gamma normalizations and
signs fixed by the right-half-plane decomposition.
-/
theorem one_div_pi_mul_re_integral_xiContourWeight_logDeriv_riemannXi_right_eq_literatureResidual
    (p : Polynomial Real) :
    (1 / Real.pi) *
        (MeasureTheory.integral volume fun t : Real =>
          guinandWeilXiContourWeight p
              ((5 / 4 : Real) + (t : Complex) * Complex.I) *
            logDeriv riemannXi
              ((5 / 4 : Real) + (t : Complex) * Complex.I)).re =
      guinandWeilPiPolynomialGaussianLiteratureResidualSide
        (guinandWeilPiEvenPolynomial p) := by
  let R : Real -> Complex := fun t =>
    guinandWeilXiContourWeight p
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
        1 / ((1 / 4 : Real) + (t : Complex) * Complex.I))
  let A : Real -> Complex := fun t =>
    guinandWeilXiContourWeight p
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      (-(Real.log Real.pi : Complex) / 2 +
        Complex.digamma
          ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I) / 2)
  let P : Real -> Complex := fun t =>
    guinandWeilXiContourWeight p
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex))
        ((5 / 4 : Real) + (t : Complex) * Complex.I)
  have hR : Integrable R := by
    exact integrable_xiContourWeight_rational_right p
  have hA : Integrable A := by
    exact integrable_xiContourWeight_archimedean_right p
  have hP : Integrable P := by
    exact integrable_xiContourWeight_vonMangoldtLSeries_right p
  have hpointwise :
      (fun t : Real =>
        guinandWeilXiContourWeight p
            ((5 / 4 : Real) + (t : Complex) * Complex.I) *
          logDeriv riemannXi
            ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
        fun t => R t + A t - P t := by
    funext t
    rw [logDeriv_riemannXi_eq_rightHalfPlaneLiteratureTerms (by norm_num)]
    dsimp only [R, A, P]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hintegral :
      (MeasureTheory.integral volume fun t : Real =>
        guinandWeilXiContourWeight p
            ((5 / 4 : Real) + (t : Complex) * Complex.I) *
          logDeriv riemannXi
            ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
        MeasureTheory.integral volume R +
          MeasureTheory.integral volume A -
            MeasureTheory.integral volume P := by
    rw [hpointwise]
    calc
      (MeasureTheory.integral volume fun t => R t + A t - P t) =
          (MeasureTheory.integral volume fun t => R t + A t) -
            MeasureTheory.integral volume P :=
        MeasureTheory.integral_sub (hR.add hA) hP
      _ = MeasureTheory.integral volume R +
          MeasureTheory.integral volume A -
            MeasureTheory.integral volume P := by
        rw [MeasureTheory.integral_add hR hA]
  have hpole :=
    one_div_pi_mul_re_integral_xiContourWeight_rational_right_eq_literaturePole p
  have hgamma :=
    one_div_pi_mul_re_integral_xiContourWeight_archimedean_right_eq_literatureGamma p
  have hprime :=
    neg_one_div_pi_mul_re_integral_xiContourWeight_vonMangoldtLSeries_right_eq_literaturePrime p
  change (1 / Real.pi) *
      (MeasureTheory.integral volume fun t : Real =>
        guinandWeilXiContourWeight p
            ((5 / 4 : Real) + (t : Complex) * Complex.I) *
          logDeriv riemannXi
            ((5 / 4 : Real) + (t : Complex) * Complex.I)).re = _
  rw [hintegral, Complex.sub_re, Complex.add_re]
  change (1 / Real.pi) *
      ((MeasureTheory.integral volume R).re +
        (MeasureTheory.integral volume A).re -
          (MeasureTheory.integral volume P).re) = _
  change (1 / Real.pi) * (MeasureTheory.integral volume R).re =
      guinandWeilPiPolynomialGaussianLiteraturePoleSide
        (guinandWeilPiEvenPolynomial p) at hpole
  change (1 / Real.pi) * (MeasureTheory.integral volume A).re =
      guinandWeilLiteratureGammaSide
        (guinandWeilPiEvenPolynomialGaussianSchwartz p) at hgamma
  change -(1 / Real.pi) * (MeasureTheory.integral volume P).re =
      guinandWeilLiteraturePrimeSide
        (guinandWeilPiEvenPolynomialGaussianSchwartz p) at hprime
  unfold guinandWeilPiEvenPolynomialGaussianSchwartz at hgamma hprime
  unfold guinandWeilPiPolynomialGaussianLiteratureResidualSide
  linear_combination hpole + hgamma + hprime

end

end RiemannHypothesisProject
