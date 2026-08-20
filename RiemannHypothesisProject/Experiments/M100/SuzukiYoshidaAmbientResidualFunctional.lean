import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaResidualExtraLogSources
import RiemannHypothesisProject.Experiments.M100.SuzukiLowFrequencyCompletionIdentification
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaResidualRepresenterReceiver

/-!
# Ambient `L²` functionals for the B3R-E residual forms

This module turns the one-extra-log fixed-source domain from B3R-E3 into
continuous ambient-`L²` pairings.  The key bridge identifies the graph inner
product against such a source with an ordinary `L²` inner product.  The
bounded remainder terms of the corrected forms can then be added at the
continuous-linear-map level.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

/-! ## The additional low-frequency fixed-source domain -/

/-- The square of the logarithmic loss is integrable.  This is the precise
low-frequency companion to E3's high-frequency extra-log estimate. -/
theorem integrable_suzukiLowFrequencyLogLoss_sq :
    Integrable (fun ξ : Real => suzukiLowFrequencyLogLoss ξ ^ 2) := by
  let major : Real → Real := fun ξ => 16 * |ξ| ^ (-1 / 2 : Real)
  have hbase : IntervalIntegrable
      (fun ξ : Real => ξ ^ (-1 / 2 : Real)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpositive : IntervalIntegrable major volume 0 1 := by
    apply (hbase.const_mul 16).congr
    intro ξ hξ
    unfold major
    rw [abs_of_nonneg]
    norm_num at hξ ⊢
    exact hξ.1.le
  have hnegative : IntervalIntegrable major volume (-1) 0 := by
    have hneg :=
      (IntervalIntegrable.iff_comp_neg (f := major) (a := 0) (b := 1)).mp
        hpositive
    have heq : Set.EqOn (fun ξ => major (-ξ)) major
        (Set.uIoc (-1 : Real) 0) := by
      intro ξ hξ
      simp only [major, abs_neg]
    have hneg' : IntervalIntegrable (fun ξ => major (-ξ)) volume
        (-1) 0 := by
      simpa only [neg_zero] using hneg.symm
    exact hneg'.congr heq
  have hmajorInterval : IntervalIntegrable major volume (-1) 1 :=
    hnegative.trans hpositive
  have hmajor : IntegrableOn major (Icc (-1 : Real) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      hmajorInterval
  have hlossOn : IntegrableOn
      (fun ξ : Real => suzukiLowFrequencyLogLoss ξ ^ 2)
      (Icc (-1 : Real) 1) := by
    apply hmajor.mono'
    · have hloss : Measurable suzukiLowFrequencyLogLoss := by
        unfold suzukiLowFrequencyLogLoss
        have hlogabs : Measurable (fun ξ : Real => Real.log |ξ|) :=
          Real.measurable_log.comp continuous_abs.measurable
        exact hlogabs.neg.indicator measurableSet_Icc
      exact (hloss.pow_const 2).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with ξ hξ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hzero : |ξ| = 0
      · have hξZero : ξ = 0 := abs_eq_zero.mp hzero
        simp [hξZero, suzukiLowFrequencyLogLoss, major]
      · have habsPos : 0 < |ξ| :=
          lt_of_le_of_ne (abs_nonneg ξ) (Ne.symm hzero)
        have habsOne : |ξ| ≤ 1 := abs_le.mpr hξ
        have hinvNonneg : 0 ≤ |ξ|⁻¹ := inv_nonneg.mpr (abs_nonneg ξ)
        have hlog := Real.log_le_rpow_div hinvNonneg
          (show 0 < (1 / 4 : Real) by norm_num)
        have hlogInv : Real.log |ξ|⁻¹ = -Real.log |ξ| := by
          rw [Real.log_inv]
        have hloss : suzukiLowFrequencyLogLoss ξ = -Real.log |ξ| := by
          unfold suzukiLowFrequencyLogLoss
          rw [Set.indicator_of_mem hξ]
        have hbound : -Real.log |ξ| ≤ 4 * |ξ| ^ (-1 / 4 : Real) := by
          rw [hlogInv, ← Real.rpow_neg_eq_inv_rpow] at hlog
          norm_num [div_eq_mul_inv] at hlog ⊢
          simpa [mul_comm] using hlog
        have hlossNonneg : 0 ≤ -Real.log |ξ| :=
          neg_nonneg.mpr (Real.log_nonpos (abs_nonneg ξ) habsOne)
        rw [hloss]
        have hsq := (sq_le_sq₀ hlossNonneg (by positivity)).mpr hbound
        calc
          (-Real.log |ξ|) ^ 2 ≤
              (4 * |ξ| ^ (-1 / 4 : Real)) ^ 2 := hsq
          _ = major ξ := by
            unfold major
            rw [mul_pow]
            ring_nf
            rw [← Real.rpow_two, ← Real.rpow_mul habsPos.le]
            norm_num
  have hindicator := hlossOn.integrable_indicator measurableSet_Icc
  apply hindicator.congr
  filter_upwards with ξ
  by_cases hξ : ξ ∈ Icc (-1 : Real) 1
  · simp [hξ]
  · rw [Set.indicator_of_notMem hξ]
    unfold suzukiLowFrequencyLogLoss
    rw [Set.indicator_of_notMem hξ, zero_pow (by norm_num)]

/-- Multiplying an endpoint Fourier square by the squared low-frequency loss
remains integrable. -/
theorem integrable_suzukiLowFrequencyLogLoss_sq_mul_endpointFourierSq
    {r : Real} (hr : 0 < r) (n : Int) :
    Integrable (fun ξ : Real =>
      suzukiLowFrequencyLogLoss ξ ^ 2 *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2) := by
  have hloss : IntegrableOn
      (fun ξ : Real => suzukiLowFrequencyLogLoss ξ ^ 2)
      (Icc (-1 : Real) 1) :=
    integrable_suzukiLowFrequencyLogLoss_sq.integrableOn
  have hproduct := hloss.mul_continuousOn
    (continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
      hr n).continuousOn isCompact_Icc
  have hindicator := hproduct.integrable_indicator measurableSet_Icc
  apply hindicator.congr
  filter_upwards with ξ
  by_cases hξ : ξ ∈ Icc (-1 : Real) 1
  · simp [hξ]
  · rw [Set.indicator_of_notMem hξ]
    unfold suzukiLowFrequencyLogLoss
    rw [Set.indicator_of_notMem hξ, zero_pow (by norm_num), zero_mul]

/-- The low-frequency loss applied once more to a fixed Fourier source. -/
def suzukiLowLossExtraWeightedFourier (v : SuzukiL2) : Real → Complex :=
  fun ξ => (suzukiLowFrequencyLogLoss ξ : Complex) *
    ((FourierTransform.fourier v : SuzukiL2) ξ)

/-- Fixed sources for which the low-frequency loss pairing is ambient-`L²`
continuous. -/
def SuzukiLowLossExtraFourierDomain : Set SuzukiL2 :=
  {v | MemLp (suzukiLowLossExtraWeightedFourier v) (2 : ENNReal) volume}

theorem suzukiLowLossExtraWeightedFourier_zero_ae :
    suzukiLowLossExtraWeightedFourier (0 : SuzukiL2) =ᵐ[volume]
      (0 : Real → Complex) := by
  have hzero : ((0 : SuzukiL2) : Real → Complex) =ᵐ[volume] 0 :=
    Lp.coeFn_zero Complex (2 : ENNReal) volume
  filter_upwards [hzero] with ξ hξ
  unfold suzukiLowLossExtraWeightedFourier
  rw [FourierTransform.fourier_zero, hξ]
  simp

theorem suzukiLowLossExtraWeightedFourier_add_ae (u v : SuzukiL2) :
    suzukiLowLossExtraWeightedFourier (u + v) =ᵐ[volume]
      (suzukiLowLossExtraWeightedFourier u +
        suzukiLowLossExtraWeightedFourier v) := by
  have hcoe := Lp.coeFn_add
    (FourierTransform.fourier u : SuzukiL2)
    (FourierTransform.fourier v : SuzukiL2)
  filter_upwards [hcoe] with ξ hξ
  unfold suzukiLowLossExtraWeightedFourier
  rw [FourierTransform.fourier_add, hξ]
  simp only [Pi.add_apply, mul_add]

theorem suzukiLowLossExtraWeightedFourier_smul_ae
    (c : Complex) (v : SuzukiL2) :
    suzukiLowLossExtraWeightedFourier (c • v) =ᵐ[volume]
      (c • suzukiLowLossExtraWeightedFourier v) := by
  have hcoe := Lp.coeFn_smul c
    (FourierTransform.fourier v : SuzukiL2)
  filter_upwards [hcoe] with ξ hξ
  unfold suzukiLowLossExtraWeightedFourier
  rw [FourierTransform.fourier_smul, hξ]
  change (suzukiLowFrequencyLogLoss ξ : Complex) *
      (c * ((FourierTransform.fourier v : SuzukiL2) ξ)) =
    c * ((suzukiLowFrequencyLogLoss ξ : Complex) *
      ((FourierTransform.fourier v : SuzukiL2) ξ))
  ring

theorem suzukiLowLossExtraFourierDomain_zero :
    SuzukiLowLossExtraFourierDomain (0 : SuzukiL2) :=
  MemLp.zero.ae_eq suzukiLowLossExtraWeightedFourier_zero_ae.symm

theorem suzukiLowLossExtraFourierDomain_add {u v : SuzukiL2}
    (hu : SuzukiLowLossExtraFourierDomain u)
    (hv : SuzukiLowLossExtraFourierDomain v) :
    SuzukiLowLossExtraFourierDomain (u + v) :=
  (hu.add hv).ae_eq
    (suzukiLowLossExtraWeightedFourier_add_ae u v).symm

theorem suzukiLowLossExtraFourierDomain_smul (c : Complex) {v : SuzukiL2}
    (hv : SuzukiLowLossExtraFourierDomain v) :
    SuzukiLowLossExtraFourierDomain (c • v) :=
  (hv.const_smul c).ae_eq
    (suzukiLowLossExtraWeightedFourier_smul_ae c v).symm

def SuzukiLowLossExtraFourierSubmodule : Submodule Complex SuzukiL2 where
  carrier := SuzukiLowLossExtraFourierDomain
  zero_mem' := suzukiLowLossExtraFourierDomain_zero
  add_mem' := suzukiLowLossExtraFourierDomain_add
  smul_mem' := suzukiLowLossExtraFourierDomain_smul

/-- Every endpoint exponential satisfies the additional low-loss domain. -/
theorem suzukiYoshidaExponentialL2_mem_lowLossExtraFourierDomain
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    SuzukiLowLossExtraFourierDomain
      (suzukiYoshidaExponentialL2 r hr n) := by
  let ordinary : Real → Complex := fun ξ =>
    (suzukiLowFrequencyLogLoss ξ : Complex) *
      FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) ξ
  have hloss : Measurable suzukiLowFrequencyLogLoss := by
    unfold suzukiLowFrequencyLogLoss
    have hlogabs : Measurable (fun ξ : Real => Real.log |ξ|) :=
      Real.measurable_log.comp continuous_abs.measurable
    exact hlogabs.neg.indicator measurableSet_Icc
  have hmeas : AEStronglyMeasurable ordinary volume :=
    ((Complex.continuous_ofReal.measurable.comp hloss).mul
      (continuous_fourier_suzukiYoshidaExponentialFunction
        hr n).measurable).aestronglyMeasurable
  have hint : Integrable (fun ξ : Real => ‖ordinary ξ‖ ^ 2) := by
    have h :=
      integrable_suzukiLowFrequencyLogLoss_sq_mul_endpointFourierSq hr n
    apply h.congr
    filter_upwards with ξ
    dsimp only [ordinary]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (suzukiLowFrequencyLogLoss_nonneg ξ), mul_pow]
  have hordinary : MemLp ordinary (2 : ENNReal) volume := by
    apply (integrable_norm_rpow_iff hmeas (by norm_num) (by simp)).mp
    simpa using hint
  apply hordinary.ae_eq
  filter_upwards [fourier_suzukiYoshidaExponentialL2_coe_ae
    hsource hr n] with ξ hξ
  unfold suzukiLowLossExtraWeightedFourier
  dsimp only [ordinary]
  rw [hξ]

theorem suzukiYoshidaEvenL2_mem_lowLossExtraFourierDomain
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Nat) :
    SuzukiLowLossExtraFourierDomain (suzukiYoshidaEvenL2 r hr n) := by
  unfold suzukiYoshidaEvenL2
  split_ifs with hn
  · exact suzukiYoshidaExponentialL2_mem_lowLossExtraFourierDomain
      hsource hr 0
  · apply suzukiLowLossExtraFourierDomain_smul
    exact suzukiLowLossExtraFourierDomain_add
      (suzukiYoshidaExponentialL2_mem_lowLossExtraFourierDomain
        hsource hr (n : Int))
      (suzukiYoshidaExponentialL2_mem_lowLossExtraFourierDomain
        hsource hr (-(n : Int)))

theorem suzukiYoshidaOddL2_mem_lowLossExtraFourierDomain
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Nat) :
    SuzukiLowLossExtraFourierDomain (suzukiYoshidaOddL2 r hr n) := by
  unfold suzukiYoshidaOddL2
  rw [sub_eq_add_neg]
  apply suzukiLowLossExtraFourierDomain_smul
  exact suzukiLowLossExtraFourierDomain_add
    (suzukiYoshidaExponentialL2_mem_lowLossExtraFourierDomain
      hsource hr (n : Int))
    (by
      simpa using
        (suzukiLowLossExtraFourierDomain_smul (-1)
          (suzukiYoshidaExponentialL2_mem_lowLossExtraFourierDomain
            hsource hr (-(n : Int)))))

/-- The exact B3R-E fixed sources also satisfy the low-loss companion
domain. -/
theorem suzukiDF6D5B3REEvenResidualSources_mem_lowLossExtraFourierDomain
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) :
    SuzukiLowLossExtraFourierDomain (suzukiDF6D5B3REEvenLowSourceL2 i) ∧
      SuzukiLowLossExtraFourierDomain
        (suzukiDF6D5B3REEvenGalerkinTrialL2 i) := by
  constructor
  · exact suzukiYoshidaEvenL2_mem_lowLossExtraFourierDomain hsource
      suzukiProjectAStar_pos (suzukiDF6D4EvenLowMode i)
  · change suzukiDF6D5B3REEvenGalerkinTrialL2 i ∈
      SuzukiLowLossExtraFourierSubmodule
    unfold suzukiDF6D5B3REEvenGalerkinTrialL2
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _
        (suzukiYoshidaEvenL2_mem_lowLossExtraFourierDomain hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))

theorem suzukiDF6D5B3REOddResidualSources_mem_lowLossExtraFourierDomain
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) :
    SuzukiLowLossExtraFourierDomain (suzukiDF6D5B3REOddLowSourceL2 i) ∧
      SuzukiLowLossExtraFourierDomain
        (suzukiDF6D5B3REOddGalerkinTrialL2 i) := by
  constructor
  · exact suzukiYoshidaOddL2_mem_lowLossExtraFourierDomain hsource
      suzukiProjectAStar_pos (suzukiDF6D4OddLowMode i)
  · change suzukiDF6D5B3REOddGalerkinTrialL2 i ∈
      SuzukiLowLossExtraFourierSubmodule
    unfold suzukiDF6D5B3REOddGalerkinTrialL2
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _
        (suzukiYoshidaOddL2_mem_lowLossExtraFourierDomain hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))

/-- The one-extra-log Fourier representative bundled as an `L²` vector. -/
def suzukiExtraLogWeightedFourierToL2
    (v : SuzukiL2) (hv : SuzukiExtraLogFourierDomain v) : SuzukiL2 :=
  hv.toLp (suzukiExtraLogWeightedFourier v)

theorem suzukiExtraLogWeightedFourierToL2_coe_ae
    (v : SuzukiL2) (hv : SuzukiExtraLogFourierDomain v) :
    ((suzukiExtraLogWeightedFourierToL2 v hv : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      suzukiExtraLogWeightedFourier v :=
  hv.coeFn_toLp

/-- The second coordinate of the closed logarithmic graph. -/
def suzukiLogRadiusLinearCompletionToWeightedFourier {r : Real} :
    SuzukiLogRadiusLinearCompletion r →L[Complex] SuzukiL2 :=
  (WithLp.sndL (2 : ENNReal) Complex SuzukiL2 SuzukiL2).comp
    ((Submodule.subtypeL SuzukiLogHilbertGraphSubmodule).comp
      (Submodule.subtypeL (SuzukiLogRadiusLinearSubmodule r)))

@[simp]
theorem suzukiLogRadiusLinearCompletionToWeightedFourier_apply
    {r : Real} (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToWeightedFourier v = v.1.1.snd :=
  rfl

/-- The second graph coordinate is the square-root logarithmic Fourier
multiplier of the physical coordinate. -/
theorem suzukiLogRadiusLinearCompletionToWeightedFourier_coe_ae
    {r : Real} (v : SuzukiLogRadiusLinearCompletion r) :
    ((suzukiLogRadiusLinearCompletionToWeightedFourier v : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      suzukiLogWeightedFourier
        (suzukiLogRadiusLinearCompletionToL2 v) := by
  have hgraph :
      FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 v) =
        suzukiLogFourierInvMultiplierCLM
          (suzukiLogRadiusLinearCompletionToWeightedFourier v) := by
    apply (suzukiLogFourierPMap_mem_graph_iff _).mp
    exact v.1.2
  exact
    (suzukiLogWeightedFourier_eq_of_fourier_eq_invMultiplier hgraph).symm

/-- With one extra logarithm on the fixed source, the second-coordinate
graph pairing becomes an ambient Fourier-space pairing. -/
theorem inner_suzukiLogWeightedFourier_eq_extraLog
    {r : Real} (u v : SuzukiLogRadiusLinearCompletion r)
    (hu : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) :
    inner Complex
        (suzukiLogRadiusLinearCompletionToWeightedFourier u)
        (suzukiLogRadiusLinearCompletionToWeightedFourier v) =
      inner Complex
        (suzukiExtraLogWeightedFourierToL2
          (suzukiLogRadiusLinearCompletionToL2 u) hu)
        (FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    suzukiLogRadiusLinearCompletionToWeightedFourier_coe_ae u,
    suzukiLogRadiusLinearCompletionToWeightedFourier_coe_ae v,
    suzukiExtraLogWeightedFourierToL2_coe_ae
      (suzukiLogRadiusLinearCompletionToL2 u) hu] with ξ huGraph hvGraph huExtra
  rw [huGraph, hvGraph, huExtra]
  unfold suzukiLogWeightedFourier suzukiExtraLogWeightedFourier
  have hnonneg := suzukiLogFourierWeight_nonneg ξ
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, map_mul,
    Complex.conj_ofReal]
  have hstarWeight :
      (starRingEnd Complex) (suzukiLogFourierWeight ξ : Complex) =
        (suzukiLogFourierWeight ξ : Complex) := by simp
  have hsqrt :
      ((Real.sqrt (suzukiLogFourierWeight ξ) : Real) : Complex) *
          ((Real.sqrt (suzukiLogFourierWeight ξ) : Real) : Complex) =
        (suzukiLogFourierWeight ξ : Complex) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnonneg]
  rw [hstarWeight]
  calc
    _ =
        (((Real.sqrt (suzukiLogFourierWeight ξ) : Real) : Complex) *
          ((Real.sqrt (suzukiLogFourierWeight ξ) : Real) : Complex)) *
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ) *
          (starRingEnd Complex)
            ((FourierTransform.fourier
              (suzukiLogRadiusLinearCompletionToL2 u) : SuzukiL2) ξ) := by
          ring
    _ = _ := by rw [hsqrt]; ring

/-- The graph inner product against a one-extra-log source is represented by
an explicit ambient `L²` vector. -/
def suzukiLogGraphInnerAmbientRepresenter
    {r : Real} (u : SuzukiLogRadiusLinearCompletion r)
    (hu : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) : SuzukiL2 :=
  suzukiLogRadiusLinearCompletionToL2 u +
    FourierTransform.fourierInv
      (suzukiExtraLogWeightedFourierToL2
        (suzukiLogRadiusLinearCompletionToL2 u) hu)

theorem suzukiLogGraphInnerAmbientRepresenter_pairing
    {r : Real} (u v : SuzukiLogRadiusLinearCompletion r)
    (hu : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) :
    inner Complex (suzukiLogGraphInnerAmbientRepresenter u hu)
        (suzukiLogRadiusLinearCompletionToL2 v) =
      inner Complex u v := by
  rw [suzukiLogGraphInnerAmbientRepresenter, inner_add_left,
    ← MeasureTheory.Lp.inner_fourier_eq
      (FourierTransform.fourierInv
        (suzukiExtraLogWeightedFourierToL2
          (suzukiLogRadiusLinearCompletionToL2 u) hu))
      (suzukiLogRadiusLinearCompletionToL2 v),
    FourierTransform.fourier_fourierInv_eq,
    ← inner_suzukiLogWeightedFourier_eq_extraLog u v hu]
  change
    inner Complex u.1.1.fst v.1.1.fst +
        inner Complex u.1.1.snd v.1.1.snd =
      inner Complex u.1.1 v.1.1
  exact (WithLp.prod_inner_apply u.1.1 v.1.1).symm

/-- The graph inner product against a fixed one-extra-log source, now as a
continuous functional on ambient `L²`. -/
def suzukiLogGraphInnerAmbientFunctional
    {r : Real} (u : SuzukiLogRadiusLinearCompletion r)
    (hu : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) :
    SuzukiL2 →L[Complex] Complex :=
  innerSL Complex (suzukiLogGraphInnerAmbientRepresenter u hu)

@[simp]
theorem suzukiLogGraphInnerAmbientFunctional_pairing
    {r : Real} (u v : SuzukiLogRadiusLinearCompletion r)
    (hu : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) :
    suzukiLogGraphInnerAmbientFunctional u hu
        (suzukiLogRadiusLinearCompletionToL2 v) = inner Complex u v := by
  exact suzukiLogGraphInnerAmbientRepresenter_pairing u v hu

/-! ## Ambient realization of every corrected-form term -/

def suzukiLowLossExtraWeightedFourierToL2
    (v : SuzukiL2) (hv : SuzukiLowLossExtraFourierDomain v) : SuzukiL2 :=
  hv.toLp (suzukiLowLossExtraWeightedFourier v)

theorem suzukiLowLossExtraWeightedFourierToL2_coe_ae
    (v : SuzukiL2) (hv : SuzukiLowLossExtraFourierDomain v) :
    ((suzukiLowLossExtraWeightedFourierToL2 v hv : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      suzukiLowLossExtraWeightedFourier v :=
  hv.coeFn_toLp

/-- The low-frequency loss energy against a fixed admissible source, as an
ambient-`L²` functional. -/
def suzukiLowFrequencyLogLossAmbientFunctional
    (u : SuzukiL2) (hu : SuzukiLowLossExtraFourierDomain u) :
    SuzukiL2 →L[Complex] Complex :=
  (innerSL Complex (suzukiLowLossExtraWeightedFourierToL2 u hu)).comp
    (MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).toContinuousLinearEquiv.toContinuousLinearMap

theorem suzukiLowFrequencyLogLossAmbientFunctional_pairing
    {r : Real} (u v : SuzukiLogRadiusLinearCompletion r)
    (hr : 0 < r)
    (hu : SuzukiLowLossExtraFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) :
    suzukiLowFrequencyLogLossAmbientFunctional
        (suzukiLogRadiusLinearCompletionToL2 u) hu
        (suzukiLogRadiusLinearCompletionToL2 v) =
      suzukiLowFrequencyLogLossEnergy hr u v := by
  unfold suzukiLowFrequencyLogLossAmbientFunctional
    suzukiLowFrequencyLogLossEnergy
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  change
    inner Complex
        (suzukiLowLossExtraWeightedFourierToL2
          (suzukiLogRadiusLinearCompletionToL2 u) hu)
        (FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) =
      inner Complex
        (suzukiLowFrequencyWeightedFourierCompletionMap hr u)
        (suzukiLowFrequencyWeightedFourierCompletionMap hr v)
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    suzukiLowLossExtraWeightedFourierToL2_coe_ae
      (suzukiLogRadiusLinearCompletionToL2 u) hu,
    suzukiLowFrequencyWeightedFourierCompletionMap_coe_ae hr u,
    suzukiLowFrequencyWeightedFourierCompletionMap_coe_ae hr v] with
      ξ huExtra huLoss hvLoss
  rw [huExtra, huLoss, hvLoss]
  unfold suzukiLowLossExtraWeightedFourier
  have hnonneg := suzukiLowFrequencyLogLoss_nonneg ξ
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, map_mul,
    Complex.conj_ofReal]
  have hstarSqrt :
      (starRingEnd Complex)
          ((Real.sqrt (suzukiLowFrequencyLogLoss ξ) : Real) : Complex) =
        ((Real.sqrt (suzukiLowFrequencyLogLoss ξ) : Real) : Complex) := by
    simp
  have hsqrt :
      ((Real.sqrt (suzukiLowFrequencyLogLoss ξ) : Real) : Complex) *
          ((Real.sqrt (suzukiLowFrequencyLogLoss ξ) : Real) : Complex) =
        (suzukiLowFrequencyLogLoss ξ : Complex) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnonneg]
  rw [hstarSqrt]
  rw [← hsqrt]
  ring

/-- The comparison form against a fixed source satisfying both required
fixed-source domains, as a continuous ambient-`L²` functional. -/
def suzukiYoshidaComparisonAmbientFunctional
    (u : SuzukiYoshidaCorrectedCommonFormDomain)
    (huExtra : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u))
    (huLow : SuzukiLowLossExtraFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) :
    SuzukiL2 →L[Complex] Complex :=
  suzukiLogGraphInnerAmbientFunctional u huExtra +
    ((suzukiSourceLogNormalizationConstant - 2 : Real) : Complex) •
      innerSL Complex (suzukiLogRadiusLinearCompletionToL2 u) -
    suzukiLowFrequencyLogLossAmbientFunctional
      (suzukiLogRadiusLinearCompletionToL2 u) huLow

@[simp]
theorem suzukiYoshidaComparisonAmbientFunctional_pairing
    (u v : SuzukiYoshidaCorrectedCommonFormDomain)
    (huExtra : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u))
    (huLow : SuzukiLowLossExtraFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) :
    suzukiYoshidaComparisonAmbientFunctional u huExtra huLow
        (suzukiLogRadiusLinearCompletionToL2 v) =
      suzukiYoshidaComparisonForm u v := by
  rw [suzukiYoshidaComparisonAmbientFunctional]
  simp only [add_apply, sub_apply, smul_apply,
    smul_eq_mul, innerSL_apply_apply,
    suzukiLogGraphInnerAmbientFunctional_pairing,
    suzukiLowFrequencyLogLossAmbientFunctional_pairing
      u v suzukiProjectAStar_pos huLow]
  rfl

/-- Ambient functional for one symmetric translation-energy term. -/
def suzukiL2SymmetricTranslationAmbientFunctional
    (t : Real) (u : SuzukiL2) : SuzukiL2 →L[Complex] Complex :=
  innerSL Complex (suzukiL2TranslateCLM t u) +
    (innerSL Complex u).comp (suzukiL2TranslateCLM t)

@[simp]
theorem suzukiL2SymmetricTranslationAmbientFunctional_pairing
    (t : Real) (u v : SuzukiL2) :
    suzukiL2SymmetricTranslationAmbientFunctional t u v =
      suzukiL2SymmetricTranslationEnergy t u v :=
  rfl

/-- Ambient functional for a finite translation block. -/
def suzukiL2FiniteTranslationAmbientFunctional
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I → Real) (u : SuzukiL2) :
    SuzukiL2 →L[Complex] Complex :=
  ∑ i ∈ s, (coefficient i : Complex) •
    suzukiL2SymmetricTranslationAmbientFunctional (shift i) u

@[simp]
theorem suzukiL2FiniteTranslationAmbientFunctional_pairing
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I → Real) (u v : SuzukiL2) :
    suzukiL2FiniteTranslationAmbientFunctional s coefficient shift u v =
      suzukiL2FiniteTranslationEnergy s coefficient shift u v := by
  simp [suzukiL2FiniteTranslationAmbientFunctional,
    suzukiL2FiniteTranslationEnergy]

/-- The corrected complete form against a fixed admissible source, as a
continuous ambient-`L²` functional. -/
def suzukiYoshidaCorrectedCompleteAmbientFunctional
    (u : SuzukiYoshidaCorrectedCommonFormDomain)
    (huExtra : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u))
    (huLow : SuzukiLowLossExtraFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) :
    SuzukiL2 →L[Complex] Complex :=
  suzukiYoshidaComparisonAmbientFunctional u huExtra huLow -
    (suzukiSourceLogNormalizationConstant : Complex) •
      innerSL Complex (suzukiLogRadiusLinearCompletionToL2 u) +
    suzukiL2FiniteTranslationAmbientFunctional
      (suzukiProjectPrimeIndexSet suzukiProjectAStar)
      suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
      (suzukiLogRadiusLinearCompletionToL2 u) -
    innerSL Complex
      (suzukiRSecondGlobalL2Operator suzukiProjectAStar
        (suzukiLogRadiusLinearCompletionToL2 u))

@[simp]
theorem suzukiYoshidaCorrectedCompleteAmbientFunctional_pairing
    (u v : SuzukiYoshidaCorrectedCommonFormDomain)
    (huExtra : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u))
    (huLow : SuzukiLowLossExtraFourierDomain
      (suzukiLogRadiusLinearCompletionToL2 u)) :
    suzukiYoshidaCorrectedCompleteAmbientFunctional u huExtra huLow
        (suzukiLogRadiusLinearCompletionToL2 v) =
      suzukiYoshidaCorrectedCompleteForm u v := by
  rw [suzukiYoshidaCorrectedCompleteAmbientFunctional]
  simp only [add_apply, sub_apply, smul_apply,
    smul_eq_mul, innerSL_apply_apply,
    suzukiYoshidaComparisonAmbientFunctional_pairing,
    suzukiL2FiniteTranslationAmbientFunctional_pairing]
  rfl

/-! ## Exact B3R-E residual functionals -/

def suzukiDF6D5B3REEvenLowSourceCompletion
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) : SuzukiYoshidaCorrectedCommonFormDomain :=
  suzukiYoshidaEvenLinearCompletionOfSource hsource
    suzukiProjectAStar_pos (suzukiDF6D4EvenLowMode i)

def suzukiDF6D5B3REOddLowSourceCompletion
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) : SuzukiYoshidaCorrectedCommonFormDomain :=
  suzukiYoshidaOddLinearCompletionOfSource hsource
    suzukiProjectAStar_pos (suzukiDF6D4OddLowMode i)

def suzukiDF6D5B3REEvenGalerkinTrialCompletion
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) : SuzukiYoshidaCorrectedCommonFormDomain :=
  ∑ k : Fin 256,
    ((suzukiDF6D4EvenGalerkinApproximant k i : Real) : Complex) •
      suzukiYoshidaEvenLinearCompletionOfSource hsource
        suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k)

def suzukiDF6D5B3REOddGalerkinTrialCompletion
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) : SuzukiYoshidaCorrectedCommonFormDomain :=
  ∑ k : Fin 256,
    ((suzukiDF6D4OddGalerkinApproximant k i : Real) : Complex) •
      suzukiYoshidaOddLinearCompletionOfSource hsource
        suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k)

@[simp]
theorem suzukiDF6D5B3REEvenLowSourceCompletion_toL2
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiDF6D5B3REEvenLowSourceCompletion hsource i) =
      suzukiDF6D5B3REEvenLowSourceL2 i := by
  unfold suzukiDF6D5B3REEvenLowSourceCompletion
    suzukiDF6D5B3REEvenLowSourceL2
  exact suzukiYoshidaEvenLinearCompletionOfSource_toL2
    hsource suzukiProjectAStar_pos (suzukiDF6D4EvenLowMode i)

@[simp]
theorem suzukiDF6D5B3REOddLowSourceCompletion_toL2
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiDF6D5B3REOddLowSourceCompletion hsource i) =
      suzukiDF6D5B3REOddLowSourceL2 i := by
  unfold suzukiDF6D5B3REOddLowSourceCompletion
    suzukiDF6D5B3REOddLowSourceL2
  exact suzukiYoshidaOddLinearCompletionOfSource_toL2
    hsource suzukiProjectAStar_pos (suzukiDF6D4OddLowMode i)

@[simp]
theorem suzukiDF6D5B3REEvenGalerkinTrialCompletion_toL2
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i) =
      suzukiDF6D5B3REEvenGalerkinTrialL2 i := by
  unfold suzukiDF6D5B3REEvenGalerkinTrialCompletion
    suzukiDF6D5B3REEvenGalerkinTrialL2
  simp only [map_sum, map_smul,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2]

@[simp]
theorem suzukiDF6D5B3REOddGalerkinTrialCompletion_toL2
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i) =
      suzukiDF6D5B3REOddGalerkinTrialL2 i := by
  unfold suzukiDF6D5B3REOddGalerkinTrialCompletion
    suzukiDF6D5B3REOddGalerkinTrialL2
  simp only [map_sum, map_smul,
    suzukiYoshidaOddLinearCompletionOfSource_toL2]

/-- The actual even post-Galerkin residual functional on global ambient
`L²`. -/
def suzukiDF6D5B3REEvenGlobalResidualFunctional
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) : SuzukiL2 →L[Complex] Complex :=
  suzukiYoshidaCorrectedCompleteAmbientFunctional
      (suzukiDF6D5B3REEvenLowSourceCompletion hsource i)
      (by
        rw [suzukiDF6D5B3REEvenLowSourceCompletion_toL2]
        exact suzukiDF6D5B3REEvenLowSourceL2_mem_extraLogFourierDomain
          hsource i)
      (by
        rw [suzukiDF6D5B3REEvenLowSourceCompletion_toL2]
        exact
          (suzukiDF6D5B3REEvenResidualSources_mem_lowLossExtraFourierDomain
            hsource i).1) -
    suzukiYoshidaComparisonAmbientFunctional
      (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i)
      (by
        rw [suzukiDF6D5B3REEvenGalerkinTrialCompletion_toL2]
        exact suzukiDF6D5B3REEvenGalerkinTrialL2_mem_extraLogFourierDomain
          hsource i)
      (by
        rw [suzukiDF6D5B3REEvenGalerkinTrialCompletion_toL2]
        exact
          (suzukiDF6D5B3REEvenResidualSources_mem_lowLossExtraFourierDomain
            hsource i).2)

/-- The actual odd post-Galerkin residual functional on global ambient
`L²`. -/
def suzukiDF6D5B3REOddGlobalResidualFunctional
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) : SuzukiL2 →L[Complex] Complex :=
  suzukiYoshidaCorrectedCompleteAmbientFunctional
      (suzukiDF6D5B3REOddLowSourceCompletion hsource i)
      (by
        rw [suzukiDF6D5B3REOddLowSourceCompletion_toL2]
        exact suzukiDF6D5B3REOddLowSourceL2_mem_extraLogFourierDomain
          hsource i)
      (by
        rw [suzukiDF6D5B3REOddLowSourceCompletion_toL2]
        exact
          (suzukiDF6D5B3REOddResidualSources_mem_lowLossExtraFourierDomain
            hsource i).1) -
    suzukiYoshidaComparisonAmbientFunctional
      (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i)
      (by
        rw [suzukiDF6D5B3REOddGalerkinTrialCompletion_toL2]
        exact suzukiDF6D5B3REOddGalerkinTrialL2_mem_extraLogFourierDomain
          hsource i)
      (by
        rw [suzukiDF6D5B3REOddGalerkinTrialCompletion_toL2]
        exact
          (suzukiDF6D5B3REOddResidualSources_mem_lowLossExtraFourierDomain
            hsource i).2)

@[simp]
theorem suzukiDF6D5B3REEvenGlobalResidualFunctional_pairing
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiDF6D5B3REEvenGlobalResidualFunctional hsource i
        (suzukiLogRadiusLinearCompletionToL2 v) =
      suzukiYoshidaCorrectedCompleteForm
          (suzukiDF6D5B3REEvenLowSourceCompletion hsource i) v -
        suzukiYoshidaComparisonForm
          (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i) v := by
  rw [suzukiDF6D5B3REEvenGlobalResidualFunctional,
    sub_apply,
    suzukiYoshidaCorrectedCompleteAmbientFunctional_pairing,
    suzukiYoshidaComparisonAmbientFunctional_pairing]

@[simp]
theorem suzukiDF6D5B3REOddGlobalResidualFunctional_pairing
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiDF6D5B3REOddGlobalResidualFunctional hsource i
        (suzukiLogRadiusLinearCompletionToL2 v) =
      suzukiYoshidaCorrectedCompleteForm
          (suzukiDF6D5B3REOddLowSourceCompletion hsource i) v -
        suzukiYoshidaComparisonForm
          (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i) v := by
  rw [suzukiDF6D5B3REOddGlobalResidualFunctional,
    sub_apply,
    suzukiYoshidaCorrectedCompleteAmbientFunctional_pairing,
    suzukiYoshidaComparisonAmbientFunctional_pairing]

/-- Restriction to the exact even parity-far ambient receiver. -/
def suzukiDF6D5B3REEvenAmbientResidualFunctional
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) : SuzukiDF6D5B3REvenAmbientFarL2 →L[Complex] Complex :=
  (suzukiDF6D5B3REEvenGlobalResidualFunctional hsource i).comp
    (Submodule.subtypeL suzukiDF6D5B3TEvenAmbientFarSubspace)

/-- Restriction to the exact odd parity-far ambient receiver. -/
def suzukiDF6D5B3REOddAmbientResidualFunctional
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) : SuzukiDF6D5B3ROddAmbientFarL2 →L[Complex] Complex :=
  (suzukiDF6D5B3REOddGlobalResidualFunctional hsource i).comp
    (Submodule.subtypeL suzukiDF6D5B3TOddAmbientFarSubspace)

/-- Modal pairing identity on the exact even B3T ambient far receiver. -/
theorem suzukiDF6D5B3REEvenAmbientResidualFunctional_mode_pairing
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) (n : SuzukiDF6D5B3RTailMode) :
    suzukiDF6D5B3REEvenAmbientResidualFunctional hsource i
        (suzukiDF6D5B3REvenAmbientMode n) =
      suzukiYoshidaCorrectedCompleteForm
          (suzukiDF6D5B3REEvenLowSourceCompletion hsource i)
          (suzukiYoshidaEvenLinearCompletionOfSource hsource
            suzukiProjectAStar_pos n.1) -
        suzukiYoshidaComparisonForm
          (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i)
          (suzukiYoshidaEvenLinearCompletionOfSource hsource
            suzukiProjectAStar_pos n.1) := by
  change suzukiDF6D5B3REEvenGlobalResidualFunctional hsource i
      (suzukiYoshidaEvenL2 suzukiProjectAStar
        suzukiProjectAStar_pos n.1) = _
  rw [← suzukiYoshidaEvenLinearCompletionOfSource_toL2
    hsource suzukiProjectAStar_pos n.1]
  exact suzukiDF6D5B3REEvenGlobalResidualFunctional_pairing hsource i _

/-- Modal pairing identity on the exact odd B3T ambient far receiver. -/
theorem suzukiDF6D5B3REOddAmbientResidualFunctional_mode_pairing
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) (n : SuzukiDF6D5B3RTailMode) :
    suzukiDF6D5B3REOddAmbientResidualFunctional hsource i
        (suzukiDF6D5B3ROddAmbientMode n) =
      suzukiYoshidaCorrectedCompleteForm
          (suzukiDF6D5B3REOddLowSourceCompletion hsource i)
          (suzukiYoshidaOddLinearCompletionOfSource hsource
            suzukiProjectAStar_pos n.1) -
        suzukiYoshidaComparisonForm
          (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i)
          (suzukiYoshidaOddLinearCompletionOfSource hsource
            suzukiProjectAStar_pos n.1) := by
  change suzukiDF6D5B3REOddGlobalResidualFunctional hsource i
      (suzukiYoshidaOddL2 suzukiProjectAStar
        suzukiProjectAStar_pos n.1) = _
  rw [← suzukiYoshidaOddLinearCompletionOfSource_toL2
    hsource suzukiProjectAStar_pos n.1]
  exact suzukiDF6D5B3REOddGlobalResidualFunctional_pairing hsource i _

end

end RiemannHypothesisProject.Experiments.M100
