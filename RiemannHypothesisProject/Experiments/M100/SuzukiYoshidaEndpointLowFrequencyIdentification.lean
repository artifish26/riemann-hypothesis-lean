import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointGraphIdentification
import RiemannHypothesisProject.Experiments.M100.SuzukiLowFrequencyCompletionIdentification

/-!
# Low-frequency multiplier on the endpoint exponential lifts

This module identifies the continuous low-frequency-loss extension on each
source-provided endpoint exponential.  The proof uses the closedness of
pointwise multiplication: the source approximation converges in the physical
Fourier coordinate and, by continuity of the extended map, in the weighted
coordinate.  Passing twice to almost-everywhere convergent subsequences forces
the two limits to retain the pointwise multiplier relation.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

/-- The continuous low-frequency extension on a direct source endpoint lift
has the concrete square-root-loss times Fourier representative. -/
theorem suzukiLowFrequencyWeightedFourierCompletionMap_directSource_coe_ae
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    ((suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiYoshidaExponentialDirectLinearCompletionOfSource
          hsource hr n) : SuzukiL2) : Real → Complex) =ᵐ[volume]
      fun xi =>
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiYoshidaExponentialL2 r hr n) : SuzukiL2) xi) := by
  let approximationLinear : Nat → SuzukiSmoothCoreLinearSubmodule r :=
    fun k =>
      ⟨(suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1,
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k).2⟩
  let uSeq : Nat → SuzukiLogRadiusLinearCompletion r := fun k =>
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r
      (approximationLinear k)
  let target : SuzukiLogRadiusLinearCompletion r :=
    suzukiYoshidaExponentialDirectLinearCompletionOfSource hsource hr n
  have hu : Tendsto uSeq atTop (nhds target) := by
    have hu' :
        Tendsto
          (fun k => suzukiSmoothCoreToLogRadiusLinearCompletion
            (suzukiYoshidaExponentialApproximationOfSource
              hsource hr n k))
          atTop (nhds target) := by
      simpa only [target] using
        (suzukiYoshidaExponentialApproximationOfSource_tendsto_linear
          hsource hr n)
    apply hu'.congr'
    exact Filter.Eventually.of_forall fun k => by
      apply suzukiLogRadiusLinearCompletionToL2_injective r
      rfl
  have hphysical :
      Tendsto
        (fun k => suzukiLogRadiusLinearCompletionToL2 (uSeq k))
        atTop
        (nhds (suzukiLogRadiusLinearCompletionToL2 target)) :=
    (suzukiLogRadiusLinearCompletionToL2.continuous.tendsto target).comp hu
  have hfourier :
      Tendsto
        (fun k => FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 (uSeq k)))
        atTop
        (nhds (FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 target))) :=
    ((MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous.tendsto
      (suzukiLogRadiusLinearCompletionToL2 target)).comp hphysical
  have hweighted :
      Tendsto
        (fun k => suzukiLowFrequencyWeightedFourierCompletionMap hr
          (uSeq k))
        atTop
        (nhds (suzukiLowFrequencyWeightedFourierCompletionMap hr target)) :=
    ((suzukiLowFrequencyWeightedFourierCompletionMap hr).continuous.tendsto
      target).comp hu
  obtain ⟨ns, hns, hfourierAe⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hfourier).exists_seq_tendsto_ae
  have hweightedSubsequence :
      Tendsto
        (fun k => suzukiLowFrequencyWeightedFourierCompletionMap hr
          (uSeq (ns k)))
        atTop
        (nhds (suzukiLowFrequencyWeightedFourierCompletionMap hr target)) :=
    hweighted.comp hns.tendsto_atTop
  obtain ⟨ms, hms, hweightedAe⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      hweightedSubsequence).exists_seq_tendsto_ae
  have hfourierAe' : ∀ᵐ xi ∂(volume : Measure Real),
      Tendsto
        (fun k =>
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2
              (uSeq (ns (ms k)))) : SuzukiL2) xi))
        atTop
        (nhds ((FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 target) : SuzukiL2) xi)) := by
    filter_upwards [hfourierAe] with xi hxi
    exact hxi.comp hms.tendsto_atTop
  have hcore : ∀ k,
      ((suzukiLowFrequencyWeightedFourierCompletionMap hr
        (uSeq k) : SuzukiL2) : Real → Complex) =ᵐ[volume]
        fun xi =>
          ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
            ((FourierTransform.fourier
              (suzukiLogRadiusLinearCompletionToL2 (uSeq k)) :
                SuzukiL2) xi) := by
    intro k
    exact suzukiLowFrequencyWeightedFourierCompletionMap_core_coe_ae
      hr (approximationLinear k)
  have hcoreAll : ∀ᵐ xi ∂(volume : Measure Real), ∀ k,
      ((suzukiLowFrequencyWeightedFourierCompletionMap hr
        (uSeq k) : SuzukiL2) : Real → Complex) xi =
          ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
            ((FourierTransform.fourier
              (suzukiLogRadiusLinearCompletionToL2 (uSeq k)) :
                SuzukiL2) xi) :=
    ae_all_iff.mpr hcore
  have htargetPhysical :
      suzukiLogRadiusLinearCompletionToL2 target =
        suzukiYoshidaExponentialL2 r hr n := by
    exact suzukiYoshidaExponentialDirectLinearCompletionOfSource_toL2
      hsource hr n
  filter_upwards [hweightedAe, hfourierAe', hcoreAll] with
      xi hweightedXi hfourierXi hcoreXi
  rw [← htargetPhysical]
  have hmul :
      Tendsto
        (fun k =>
          ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
            ((FourierTransform.fourier
              (suzukiLogRadiusLinearCompletionToL2
                (uSeq (ns (ms k)))) : SuzukiL2) xi))
        atTop
        (nhds
          (((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
            ((FourierTransform.fourier
              (suzukiLogRadiusLinearCompletionToL2 target) : SuzukiL2)
                xi))) :=
    tendsto_const_nhds.mul hfourierXi
  have hweightedXi' :
      Tendsto
        (fun k =>
          ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
            ((FourierTransform.fourier
              (suzukiLogRadiusLinearCompletionToL2
                (uSeq (ns (ms k)))) : SuzukiL2) xi))
        atTop
        (nhds
          ((suzukiLowFrequencyWeightedFourierCompletionMap hr target :
            SuzukiL2) xi)) := by
    apply hweightedXi.congr'
    exact Filter.Eventually.of_forall fun k =>
      hcoreXi (ns (ms k))
  exact tendsto_nhds_unique hweightedXi' hmul

/-- Canonical-lift form of the endpoint low-frequency identification used by
the comparison kernel. -/
theorem suzukiLowFrequencyWeightedFourierCompletionMap_source_coe_ae
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    ((suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource hr n) : SuzukiL2) : Real → Complex) =ᵐ[volume]
      fun xi =>
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiYoshidaExponentialL2 r hr n) : SuzukiL2) xi) := by
  rw [suzukiYoshidaExponentialLinearCompletionOfSource_eq_direct]
  exact
    suzukiLowFrequencyWeightedFourierCompletionMap_directSource_coe_ae
      hsource hr n

end

end RiemannHypothesisProject.Experiments.M100
