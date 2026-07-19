import RiemannHypothesisProject.GuinandWeilConcrete.XiDivisor

/-!
# Finite weighted xi rectangle identity

This module specializes the generic weighted rectangle argument principle to
the entire Riemann xi function and the polynomial-Gaussian Guinand-Weil
contour weight.  The only contour-specific hypothesis is that xi has no zero
on the four rectangle sides.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Complex Set

/-- The finite multiplicity-aware weighted xi rectangle identity.  Every xi
zero in the rectangle occurs exactly once in the divisor support and carries
its full analytic multiplicity. -/
theorem guinandWeilXi_normalizedRectangleIntegral_eq_weightedZeroSum
    (p : Polynomial Real) {z w : Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hboundary : ∀ s ∈ guinandWeilRectangleBorder z w,
      riemannXi s ≠ 0) :
    guinandWeilNormalizedRectangleIntegral
        (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
        z w =
      riemannXiRectangleWeightedZeroSum
        (guinandWeilXiContourWeight p) z w := by
  have hidentity :=
    guinandWeilNormalizedRectangleIntegral_weight_mul_logDeriv_eq_sum
      (H := guinandWeilXiContourWeight p)
      (f := riemannXi)
      (S := riemannXiRectangleDivisorSupport z w)
      hzre hzim
      ((analyticOnNhd_guinandWeilXiContourWeight p).mono (Set.subset_univ _))
      (analyticOnNhd_riemannXi (Rectangle z w))
      (fun s _hs => analyticOrderAt_riemannXi_ne_top s)
      (fun _s hs =>
        (MeromorphicOn.divisor riemannXi (Rectangle z w)).supportWithinDomain
          (mem_riemannXiRectangleDivisorSupport.mp hs))
      (fun s hs => mem_riemannXiRectangleDivisorSupport_iff.trans
        (and_iff_right hs))
      hboundary
  rw [hidentity]
  unfold riemannXiRectangleWeightedZeroSum
  rw [Finset.sum_attach (riemannXiRectangleDivisorSupport z w)
    (fun s => (analyticOrderNatAt riemannXi s : Complex) *
      guinandWeilXiContourWeight p s)]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- Four-side form of the finite weighted xi rectangle identity.  The signs
record the positive orientation: bottom minus top plus right minus left. -/
theorem guinandWeilXi_rectangleBoundary_decomposition_eq_weightedZeroSum
    (p : Polynomial Real) {z w : Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hboundary : ∀ s ∈ guinandWeilRectangleBorder z w,
      riemannXi s ≠ 0) :
    (1 / (2 * Real.pi * Complex.I)) *
        (guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            z.re w.re z.im -
          guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            z.re w.re w.im +
          guinandWeilVerticalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            w.re z.im w.im -
          guinandWeilVerticalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            z.re z.im w.im) =
      riemannXiRectangleWeightedZeroSum
        (guinandWeilXiContourWeight p) z w := by
  simpa only [guinandWeilNormalizedRectangleIntegral,
    guinandWeilRectangleIntegral] using
    guinandWeilXi_normalizedRectangleIntegral_eq_weightedZeroSum
      p hzre hzim hboundary

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
