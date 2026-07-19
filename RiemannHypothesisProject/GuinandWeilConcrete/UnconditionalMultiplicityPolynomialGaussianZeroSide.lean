import RiemannHypothesisProject.GuinandWeilConcrete.MultiplicityPolynomialGaussianZeroSide
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiJensen

/-!
# Unconditional multiplicity-aware polynomial-Gaussian zero side

This module consumes the xi/Jensen canonical multiplicity-growth theorem at
the actual all-zero summability, window-limit, and complementary-tail
endpoints.  No Bellotti-Wong source assumption remains in these statements.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Unconditional absolute convergence of the actual completed-zeta
polynomial-Gaussian zero side with analytic multiplicity. -/
theorem summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_unconditional
    (p : Polynomial Complex) :
    Summable (fun rho : ZetaZeroSubtype =>
      norm
        (zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) :=
  summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_of_growth
    riemannXiCanonicalMultiplicityPolynomialGrowth p

/-- Unconditional signed convergence of the multiplicity-weighted zero
side. -/
theorem summable_multiplicityPolynomialGaussianCompletedZetaZeroWeight_unconditional
    (p : Polynomial Complex) :
    Summable (fun rho : ZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho *
        guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) :=
  summable_multiplicityPolynomialGaussianCompletedZetaZeroWeight_of_growth
    riemannXiCanonicalMultiplicityPolynomialGrowth p

/-- Unconditional convergence of compact-exhaustion zero-window sums. -/
theorem tendsto_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_unconditional
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        exhaustion.zetaZeroWindowSum n (fun rho : ZetaZeroSubtype =>
          zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho))
      Filter.atTop
      (nhds (∑' rho : ZetaZeroSubtype,
        zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) :=
  tendsto_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_of_growth
    riemannXiCanonicalMultiplicityPolynomialGrowth p exhaustion

/-- Unconditional vanishing of the absolute complementary zero tail. -/
theorem tendsto_tsum_norm_multiplicityPolynomialGaussianCompletedZetaZero_compl_unconditional
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        ∑' rho :
          {rho : ZetaZeroSubtype // rho ∉ exhaustion.zetaZeroSubtypeFinset n},
          norm
            (zetaZeroMultiplicityReal rho.1 *
              guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1))
      Filter.atTop (nhds 0) :=
  tendsto_tsum_norm_multiplicityPolynomialGaussianCompletedZetaZero_compl_of_growth
    riemannXiCanonicalMultiplicityPolynomialGrowth p exhaustion

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
