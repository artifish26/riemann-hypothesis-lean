import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaBurnolAnalyticAdmissibility
import RiemannHypothesisProject.GuinandWeilConcrete.XiDivisor

/-!
# M100-DF6F finite Burnol xi-contour identity

This module begins the remaining compact-support Guinand--Weil proof itself.
The smooth-core Burnol source is pulled back to xi coordinates, where its
proved entire extension permits the weighted rectangle argument principle.
The resulting finite divisor sum is then identified with the exact
multiplicity-aware Burnol zero weights used by the project.

No infinite-contour limit or source formula is assumed here.  The remaining
analytic work is horizontal-edge decay, convergence of the vertical sides,
and evaluation of the right vertical integral.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Complex Set
open SchwartzLineTestFunction
open ComplexCompactExhaustion

/-- The smooth-core Burnol source in the xi variable. -/
def suzukiSmoothCoreBurnolXiContourWeight
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (s : Complex) : Complex :=
  burnolFourierLaplaceSource (suzukiProjectBase v.1)
    ((s - (1 / 2 : Complex)) / Complex.I)

/-- The smooth-core Burnol xi-contour weight is entire. -/
theorem differentiable_suzukiSmoothCoreBurnolXiContourWeight
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Differentiable Complex (suzukiSmoothCoreBurnolXiContourWeight v) := by
  exact
    (differentiable_burnolFourierLaplaceSource_suzukiProjectBase
      suzukiProjectAStar_pos.le v).comp
      (by fun_prop : Differentiable Complex
        (fun s : Complex => (s - (1 / 2 : Complex)) / Complex.I))

/-- Analytic form of the entire contour-weight theorem. -/
theorem analyticOnNhd_suzukiSmoothCoreBurnolXiContourWeight
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    AnalyticOnNhd Complex (suzukiSmoothCoreBurnolXiContourWeight v) univ := by
  exact Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (differentiable_suzukiSmoothCoreBurnolXiContourWeight v)

/-- The finite weighted xi rectangle identity for the actual smooth-core
Burnol source. Every xi zero in the rectangle occurs with its analytic
multiplicity. -/
theorem suzukiSmoothCoreBurnolXi_normalizedRectangleIntegral_eq_weightedZeroSum
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    {z w : Complex}
    (hzre : z.re <= w.re) (hzim : z.im <= w.im)
    (hboundary : ∀ s ∈ guinandWeilRectangleBorder z w,
      riemannXi s ≠ 0) :
    guinandWeilNormalizedRectangleIntegral
        (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
          logDeriv riemannXi s)
        z w =
      riemannXiRectangleWeightedZeroSum
        (suzukiSmoothCoreBurnolXiContourWeight v) z w := by
  have hidentity :=
    guinandWeilNormalizedRectangleIntegral_weight_mul_logDeriv_eq_sum
      (H := suzukiSmoothCoreBurnolXiContourWeight v)
      (f := riemannXi)
      (S := riemannXiRectangleDivisorSupport z w)
      hzre hzim
      ((analyticOnNhd_suzukiSmoothCoreBurnolXiContourWeight v).mono
        (subset_univ _))
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
      suzukiSmoothCoreBurnolXiContourWeight v s)]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- The real part of the finite xi divisor sum is exactly the corresponding
finite sum of the project's completed-zeta Burnol weights. -/
theorem re_suzukiSmoothCoreBurnolXi_weightedZeroSum_eq_zeroWeight_sum
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (z w : Complex) :
    (riemannXiRectangleWeightedZeroSum
        (suzukiSmoothCoreBurnolXiContourWeight v) z w).re =
      ∑ s ∈ (riemannXiRectangleDivisorSupport z w).attach,
        guinandWeilBurnolLiteratureZeroWeight
          (suzukiProjectBase v.1)
          (riemannXiRectangleZetaZero z w s s.property) := by
  rw [riemannXiRectangleWeightedZeroSum_eq_zetaZeroMultiplicity]
  rw [← Complex.reCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  have hnotTrivial :
      ¬ IsTrivialZetaZero
        (riemannXiRectangleZetaZero z w s s.property : Complex) :=
    not_isTrivialZetaZero_riemannXiRectangleZetaZero z w s s.property
  have hrho :
      (riemannXiRectangleZetaZero z w s s.property : Complex) = (s : Complex) :=
    rfl
  simp only [guinandWeilBurnolLiteratureZeroWeight, if_neg hnotTrivial]
  rw [hrho]
  simp [suzukiSmoothCoreBurnolXiContourWeight,
    zetaZeroMultiplicityReal, riemannWeilZeroArgument,
    Complex.mul_re]

end

end RiemannHypothesisProject.Experiments.M100
