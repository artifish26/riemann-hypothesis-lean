import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCorrectedForms
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

/-!
# Concrete low-frequency multiplier on the completed graph domain

This module identifies the continuous low-frequency-loss extension on every
element of the logarithmic graph completion.  The proof approximates by the
dense smooth core and uses almost-everywhere convergent Fourier and weighted
subsequences to retain the pointwise multiplier relation at the limit.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- On the smooth core, the extended low-frequency map is represented by the
square-root loss multiplier applied to the `L²` Fourier coordinate. -/
theorem suzukiLowFrequencyWeightedFourierCompletionMap_core_coe_ae
    {r : Real} (hr : 0 < r)
    (v : SuzukiSmoothCoreLinearSubmodule r) :
    ((suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v) :
          SuzukiL2) : Real → Complex) =ᵐ[volume]
      fun xi =>
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2
              (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v)) :
                SuzukiL2) xi) := by
  rw [suzukiLowFrequencyWeightedFourierCompletionMap_core]
  change
    ((suzukiLowFrequencyWeightedFourierToL2 hr v : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      fun xi =>
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiSmoothCoreToL2
              (suzukiSmoothCoreLinearSubmoduleAsCore v)) : SuzukiL2) xi)
  have hsmoothToLp :
      suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore v) =
        v.1.toLp (2 : ENNReal) (volume : Measure Real) := by
    apply Lp.ext
    filter_upwards [
      (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp,
      SchwartzMap.coeFn_toLp v.1 (2 : ENNReal)
        (volume : Measure Real)] with xi hleft hright
    exact hleft.trans hright.symm
  have hfourier :
      FourierTransform.fourier
          (suzukiSmoothCoreToL2
            (suzukiSmoothCoreLinearSubmoduleAsCore v)) =
        (SchwartzMap.fourierTransformCLM Complex v.1).toLp
          (2 : ENNReal) (volume : Measure Real) := by
    rw [hsmoothToLp]
    simpa only [SchwartzMap.fourierTransformCLM_apply] using
      (SchwartzMap.toLp_fourier_eq v.1)
  have hfourierCoe :
      ((FourierTransform.fourier
        (suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore v)) : SuzukiL2) :
            Real → Complex) =ᵐ[volume]
        SchwartzMap.fourierTransformCLM Complex v.1 := by
    rw [hfourier]
    exact ((SchwartzMap.fourierTransformCLM Complex v.1).memLp
      (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
  have hweighted :=
    (suzukiLowFrequencyWeightedFourier_memLp hr v).coeFn_toLp
  simp only [suzukiLowFrequencyWeightedFourierToL2]
  filter_upwards [hweighted, hfourierCoe] with xi hweighted hfourierCoe
  rw [hweighted, hfourierCoe]
  rfl

/-- Every completed graph element retains the concrete low-frequency
multiplier relation.  No endpoint source representation or surjectivity of
the physical projection is used. -/
theorem suzukiLowFrequencyWeightedFourierCompletionMap_coe_ae
    {r : Real} (hr : 0 < r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    ((suzukiLowFrequencyWeightedFourierCompletionMap hr v : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      fun xi =>
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) xi) := by
  have hv : v ∈ closure
      (Set.range (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r)) := by
    rw [(suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange r).closure_eq]
    exact Set.mem_univ v
  obtain ⟨uSeq, huRange, hu⟩ := mem_closure_iff_seq_limit.mp hv
  choose core hcore using huRange
  have hu' : Tendsto
      (fun n => suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r (core n))
      atTop (nhds v) := by
    apply hu.congr'
    exact Eventually.of_forall fun n => (hcore n).symm
  have hphysical : Tendsto
      (fun n => suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r (core n)))
      atTop (nhds (suzukiLogRadiusLinearCompletionToL2 v)) :=
    (suzukiLogRadiusLinearCompletionToL2.continuous.tendsto v).comp hu'
  have hfourier : Tendsto
      (fun n => FourierTransform.fourier
        (suzukiLogRadiusLinearCompletionToL2
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r (core n))))
      atTop
      (nhds (FourierTransform.fourier
        (suzukiLogRadiusLinearCompletionToL2 v))) :=
    ((MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous.tendsto
      (suzukiLogRadiusLinearCompletionToL2 v)).comp hphysical
  have hweighted : Tendsto
      (fun n => suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r (core n)))
      atTop (nhds (suzukiLowFrequencyWeightedFourierCompletionMap hr v)) :=
    ((suzukiLowFrequencyWeightedFourierCompletionMap hr).continuous.tendsto v).comp hu'
  obtain ⟨ns, hns, hfourierAe⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hfourier).exists_seq_tendsto_ae
  have hweightedSubsequence : Tendsto
      (fun n => suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r (core (ns n))))
      atTop (nhds (suzukiLowFrequencyWeightedFourierCompletionMap hr v)) :=
    hweighted.comp hns.tendsto_atTop
  obtain ⟨ms, hms, hweightedAe⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      hweightedSubsequence).exists_seq_tendsto_ae
  have hfourierAe' : ∀ᵐ xi ∂(volume : Measure Real),
      Tendsto
        (fun k =>
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2
              (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r
                (core (ns (ms k))))) : SuzukiL2) xi))
        atTop
        (nhds ((FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) xi)) := by
    filter_upwards [hfourierAe] with xi hxi
    exact hxi.comp hms.tendsto_atTop
  have hcoreCoe : ∀ n,
      ((suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r (core n)) :
          SuzukiL2) : Real → Complex) =ᵐ[volume]
        fun xi =>
          ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
            ((FourierTransform.fourier
              (suzukiLogRadiusLinearCompletionToL2
                (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r
                  (core n))) : SuzukiL2) xi) := by
    intro n
    exact suzukiLowFrequencyWeightedFourierCompletionMap_core_coe_ae
      hr (core n)
  have hcoreAll : ∀ᵐ xi ∂(volume : Measure Real), ∀ n,
      ((suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r (core n)) :
          SuzukiL2) : Real → Complex) xi =
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2
              (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r
                (core n))) : SuzukiL2) xi) :=
    ae_all_iff.mpr hcoreCoe
  filter_upwards [hweightedAe, hfourierAe', hcoreAll] with
      xi hweightedXi hfourierXi hcoreXi
  have hmul : Tendsto
      (fun k =>
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2
              (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r
                (core (ns (ms k))))) : SuzukiL2) xi))
      atTop
      (nhds
        (((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) xi))) :=
    tendsto_const_nhds.mul hfourierXi
  have hweightedXi' : Tendsto
      (fun k =>
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2
              (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r
                (core (ns (ms k))))) : SuzukiL2) xi))
      atTop
      (nhds
        ((suzukiLowFrequencyWeightedFourierCompletionMap hr v : SuzukiL2)
          xi)) := by
    apply hweightedXi.congr'
    exact Eventually.of_forall fun k => hcoreXi (ns (ms k))
  exact tendsto_nhds_unique hweightedXi' hmul

end
end RiemannHypothesisProject.Experiments.M100
