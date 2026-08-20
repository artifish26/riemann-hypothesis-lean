import RiemannHypothesisProject.Experiments.M100.SuzukiSingularFourierIdentity
import RiemannHypothesisProject.Experiments.M100.SuzukiCosineIntegralConstant
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# M100-DF6D2 singular shifted completion

This module compares the exact singular/source form norm on a positive-radius
smooth core with the closed logarithmic multiplier graph norm.  The only
non-pointwise input is the compact-support estimate controlling the negative
low-frequency logarithm by the ambient `L²` norm.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The fixed normalization constant separating Suzuki's source multiplier
from `log |ξ|`. -/
def suzukiSourceLogNormalizationConstant : Real :=
  Real.log (2 * Real.pi) + Real.eulerMascheroniConstant

/-- The negative low-frequency part of `log |ξ|`, cut off to `[-1,1]`. -/
def suzukiLowFrequencyLogLoss (ξ : Real) : Real :=
  (Icc (-1 : Real) 1).indicator (fun t => -Real.log |t|) ξ

theorem suzukiLowFrequencyLogLoss_nonneg (ξ : Real) :
    0 ≤ suzukiLowFrequencyLogLoss ξ := by
  unfold suzukiLowFrequencyLogLoss
  by_cases hξ : ξ ∈ Icc (-1 : Real) 1
  · rw [Set.indicator_of_mem hξ]
    have habs : |ξ| ≤ 1 := abs_le.mpr hξ
    exact neg_nonneg.mpr (Real.log_nonpos (abs_nonneg ξ) habs)
  · rw [Set.indicator_of_notMem hξ]

theorem suzukiLowFrequencyLogLoss_eq_zero_of_one_le_abs
    {ξ : Real} (hξ : 1 ≤ |ξ|) :
    suzukiLowFrequencyLogLoss ξ = 0 := by
  unfold suzukiLowFrequencyLogLoss
  by_cases heq : |ξ| = 1
  · have hmem : ξ ∈ Icc (-1 : Real) 1 := abs_le.mp heq.le
    rw [Set.indicator_of_mem hmem]
    rw [heq, Real.log_one, neg_zero]
  · rw [Set.indicator_of_notMem]
    exact fun hmem => heq (le_antisymm (abs_le.mpr hmem) hξ)

theorem suzukiPosLog_sub_lowFrequencyLogLoss (ξ : Real) :
    Real.posLog |ξ| - suzukiLowFrequencyLogLoss ξ = Real.log |ξ| := by
  rcases le_total |ξ| 1 with hξ | hξ
  · have hmem : ξ ∈ Icc (-1 : Real) 1 := abs_le.mp hξ
    rw [suzukiLowFrequencyLogLoss, Set.indicator_of_mem hmem,
      (Real.posLog_eq_zero_iff |ξ|).2]
    · ring
    · simpa only [abs_abs] using hξ
  · rw [suzukiLowFrequencyLogLoss_eq_zero_of_one_le_abs hξ,
      sub_zero, Real.posLog_eq_log]
    simpa only [abs_abs] using hξ

theorem integrable_suzukiLowFrequencyLogLoss :
    Integrable suzukiLowFrequencyLogLoss := by
  have hinterval : IntervalIntegrable
      (fun ξ : Real => -Real.log |ξ|) volume (-1) 1 := by
    have hlog : IntervalIntegrable Real.log volume (-1) 1 :=
      intervalIntegral.intervalIntegrable_log'
    apply hlog.neg.congr
    intro ξ _hξ
    simp only [Pi.neg_apply, Real.log_abs]
  have hon : IntegrableOn (fun ξ : Real => -Real.log |ξ|)
      (Icc (-1) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 hinterval
  exact hon.integrable_indicator measurableSet_Icc

theorem integral_suzukiLowFrequencyLogLoss :
    ∫ ξ : Real, suzukiLowFrequencyLogLoss ξ = 2 := by
  have hpositive :
      (∫ ξ in (0 : Real)..1, -Real.log |ξ|) = 1 := by
    simp only [Real.log_abs]
    rw [intervalIntegral.integral_neg, integral_log]
    norm_num
  have hnegative :
      (∫ ξ in (-1 : Real)..0, -Real.log |ξ|) = 1 := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun ξ : Real => -Real.log |ξ|) (a := 0) (b := 1)
    simp only [abs_neg] at hcomp
    simpa only [neg_zero] using hcomp.symm.trans hpositive
  unfold suzukiLowFrequencyLogLoss
  rw [integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : Real) ≤ 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (b := (0 : Real))]
  · rw [hnegative, hpositive]
    norm_num
  · have hinterval : IntervalIntegrable
        (fun ξ : Real => -Real.log |ξ|) volume (-1) 1 := by
      have hlog : IntervalIntegrable Real.log volume (-1) 1 :=
        intervalIntegral.intervalIntegrable_log'
      apply hlog.neg.congr
      intro ξ _hξ
      simp only [Pi.neg_apply, Real.log_abs]
    exact hinterval.mono_set (by grind [uIcc])
  · have hinterval : IntervalIntegrable
        (fun ξ : Real => -Real.log |ξ|) volume (-1) 1 := by
      have hlog : IntervalIntegrable Real.log volume (-1) 1 :=
        intervalIntegral.intervalIntegrable_log'
      apply hlog.neg.congr
      intro ξ _hξ
      simp only [Pi.neg_apply, Real.log_abs]
    exact hinterval.mono_set (by grind [uIcc])

/-- Squared `L²` norm of a concrete representative, expressed as its
pointwise norm-square integral. -/
theorem norm_sq_toLp_eq_integral_norm_sq
    (f : Real → Complex) (hf : MemLp f (2 : ENNReal) volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : Real, ‖f x‖ ^ 2 := by
  let F : SuzukiL2 := hf.toLp f
  have hself : (inner Complex F F).re = ‖F‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) F
  have hintegrable : Integrable (fun x : Real => inner Complex (F x) (F x)) :=
    L2.integrable_inner F F
  calc
    ‖hf.toLp f‖ ^ 2 = (inner Complex F F).re := hself.symm
    _ = (∫ x : Real, inner Complex (F x) (F x)).re := by
      rw [L2.inner_def]
    _ = ∫ x : Real, (inner Complex (F x) (F x)).re :=
      (integral_re hintegrable).symm
    _ = ∫ x : Real, ‖f x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
      simpa using (inner_self_eq_norm_sq (𝕜 := Complex) (f x))

/-- Compact support gives the sharp interval Cauchy--Schwarz estimate needed
for the low-frequency Fourier bound. -/
theorem sq_norm_suzukiSmoothCore_toLp_one_le
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    ‖v.1.toLp (1 : ENNReal) volume‖ ^ 2 ≤
      (2 * a) * ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
  let μ : Measure Real := volume.restrict (Icc (-a) a)
  have hfinite : μ Set.univ ≠ ∞ := by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ]
    rw [Real.volume_Icc]
    simp
  letI : IsFiniteMeasure μ :=
    IsFiniteMeasure.mk hfinite.lt_top
  have hvμ : MemLp v.1 (2 : ENNReal) μ :=
    (v.1.memLp (2 : ENNReal) volume).restrict (Icc (-a) a)
  have hone : MemLp (fun _ : Real => (1 : Complex))
      (2 : ENNReal) μ := memLp_const 1
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := fun _ : Real => (1 : Complex)) (g := v.1)
    Real.HolderConjugate.two_two (by simpa using hone) (by simpa using hvμ)
  have hsupport : ∀ x, x ∉ Icc (-a) a → v.1 x = 0 := by
    intro x hx
    by_contra hne
    exact hx ⟨(v.2 hne).1.le, (v.2 hne).2.le⟩
  have hleft :
      (∫ x : Real, ‖v.1 x‖) = ∫ x : Real, ‖v.1 x‖ ∂μ := by
    dsimp only [μ]
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (-a) a
    · simp only [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupport x hx, norm_zero]
  have honeIntegral :
      (∫ _x : Real, ‖(1 : Complex)‖ ^ (2 : Real) ∂μ) = 2 * a := by
    dsimp only [μ]
    simp [ha.le]
    ring
  have hvIntegral :
      (∫ x : Real, ‖v.1 x‖ ^ (2 : Real) ∂μ) =
        ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
    dsimp only [μ]
    rw [← integral_indicator measurableSet_Icc]
    have hglobal :
        (∫ x : Real, ‖v.1 x‖ ^ 2) =
          ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
      symm
      exact norm_sq_toLp_eq_integral_norm_sq v.1
        (v.1.memLp (2 : ENNReal) volume)
    rw [← hglobal]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (-a) a
    · simp only [Set.indicator_of_mem hx]
      rw [Real.rpow_two]
    · rw [Set.indicator_of_notMem hx, hsupport x hx, norm_zero,
        zero_pow (by norm_num : (2 : Nat) ≠ 0)]
  simp only [norm_one, one_mul] at hholder
  have honeIntegral' :
      (∫ _x : Real, (1 : Real) ^ (2 : Real) ∂μ) = 2 * a := by
    simpa only [norm_one] using honeIntegral
  rw [← hleft, ← SchwartzMap.norm_toLp_one, honeIntegral', hvIntegral] at hholder
  have hroot : 0 ≤ (2 * a) ^ (1 / (2 : Real)) :=
    Real.rpow_nonneg (by positivity) _
  have hvroot : 0 ≤ (‖suzukiSmoothCoreToL2 v‖ ^ 2) ^ (1 / (2 : Real)) :=
    Real.rpow_nonneg (sq_nonneg _) _
  have hsqRoot : ((2 * a) ^ (1 / (2 : Real))) ^ 2 = 2 * a := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (2 * a))]
    norm_num
  have hvSqRoot :
      ((‖suzukiSmoothCoreToL2 v‖ ^ 2) ^ (1 / (2 : Real))) ^ 2 =
        ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (sq_nonneg _)]
    norm_num
  have hsquare := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hroot hvroot)).2 hholder
  rw [mul_pow, hsqRoot, hvSqRoot] at hsquare
  exact hsquare

theorem norm_sq_fourier_suzukiSmoothCore_le
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) (ξ : Real) :
    ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2 ≤
      (2 * a) * ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
  have hpoint := SchwartzMap.norm_fourier_apply_le_toLp_one v.1 ξ
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hpoint
  exact hsquare.trans (sq_norm_suzukiSmoothCore_toLp_one_le ha v)

/-- The low-frequency logarithmic loss in the exact source form. -/
def suzukiLowFrequencyLogLossForm
    (v : SchwartzLineTestFunction) : Real :=
  ∫ ξ : Real, suzukiLowFrequencyLogLoss ξ *
    ‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2

theorem integrable_suzukiLowFrequencyLogLossFormIntegrand
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    Integrable (fun ξ : Real => suzukiLowFrequencyLogLoss ξ *
      ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2) := by
  let C : Real := (2 * a) * ‖suzukiSmoothCoreToL2 v‖ ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hmajor : Integrable (fun ξ : Real =>
      C * suzukiLowFrequencyLogLoss ξ) :=
    integrable_suzukiLowFrequencyLogLoss.const_mul C
  apply hmajor.mono'
  · have hloss : Measurable suzukiLowFrequencyLogLoss := by
      unfold suzukiLowFrequencyLogLoss
      have hlogabs : Measurable (fun ξ : Real => Real.log |ξ|) :=
        Real.measurable_log.comp continuous_abs.measurable
      exact (hlogabs.neg).indicator measurableSet_Icc
    exact (hloss.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (suzukiLowFrequencyLogLoss_nonneg ξ) (sq_nonneg _))]
    calc
      suzukiLowFrequencyLogLoss ξ *
          ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2 ≤
          suzukiLowFrequencyLogLoss ξ * C :=
        mul_le_mul_of_nonneg_left
          (norm_sq_fourier_suzukiSmoothCore_le ha v ξ)
          (suzukiLowFrequencyLogLoss_nonneg ξ)
      _ = C * suzukiLowFrequencyLogLoss ξ := by ring

theorem suzukiLowFrequencyLogLossForm_nonneg
    (v : SchwartzLineTestFunction) :
    0 ≤ suzukiLowFrequencyLogLossForm v := by
  unfold suzukiLowFrequencyLogLossForm
  exact integral_nonneg fun ξ => mul_nonneg
    (suzukiLowFrequencyLogLoss_nonneg ξ) (sq_nonneg _)

theorem suzukiLowFrequencyLogLossForm_le
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    suzukiLowFrequencyLogLossForm v.1 ≤
      4 * a * ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
  let C : Real := (2 * a) * ‖suzukiSmoothCoreToL2 v‖ ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hmajor : Integrable (fun ξ : Real =>
      C * suzukiLowFrequencyLogLoss ξ) :=
    integrable_suzukiLowFrequencyLogLoss.const_mul C
  have hminor := integrable_suzukiLowFrequencyLogLossFormIntegrand ha v
  calc
    suzukiLowFrequencyLogLossForm v.1 ≤
        ∫ ξ : Real, C * suzukiLowFrequencyLogLoss ξ := by
      unfold suzukiLowFrequencyLogLossForm
      apply integral_mono hminor hmajor
      intro ξ
      calc
        suzukiLowFrequencyLogLoss ξ *
            ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2 ≤
            suzukiLowFrequencyLogLoss ξ * C :=
          mul_le_mul_of_nonneg_left
            (norm_sq_fourier_suzukiSmoothCore_le ha v ξ)
            (suzukiLowFrequencyLogLoss_nonneg ξ)
        _ = C * suzukiLowFrequencyLogLoss ξ := by ring
    _ = C * 2 := by
      rw [integral_const_mul, integral_suzukiLowFrequencyLogLoss]
    _ = 4 * a * ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
      dsimp only [C]
      ring

theorem integrable_suzukiLogFourierWeight_normSq
    (v : SchwartzLineTestFunction) :
    Integrable (fun ξ : Real =>
      suzukiLogFourierWeight ξ *
        ‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2) := by
  let f : SchwartzLineTestFunction :=
    SchwartzMap.fourierTransformCLM Complex v
  have hweighted := schwartz_memLp_suzukiLogWeighted f
  have hpow := hweighted.integrable_norm_pow (by norm_num)
  apply hpow.congr
  filter_upwards with ξ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (suzukiLogFourierWeight_nonneg ξ)]

theorem integral_normSq_fourier_suzukiSmoothCore
    {a : Real} (v : SuzukiSmoothCore a) :
    (∫ ξ : Real,
        ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2) =
      ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
  calc
    (∫ ξ : Real,
        ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2) =
        ∫ x : Real, ‖v.1 x‖ ^ 2 :=
      SchwartzMap.integral_norm_sq_fourier v.1
    _ = ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
      symm
      exact norm_sq_toLp_eq_integral_norm_sq v.1
        (v.1.memLp (2 : ENNReal) volume)

theorem suzukiLogWeightedFourier_smoothCore_ae
    {a : Real} (v : SuzukiSmoothCore a) :
    (suzukiLogWeightedFourier (suzukiSmoothCoreToL2 v)) =ᵐ[volume]
      fun ξ : Real =>
        ((Real.sqrt (suzukiLogFourierWeight ξ) : Real) : Complex) *
          SchwartzMap.fourierTransformCLM Complex v.1 ξ := by
  have hsmoothToLp :
      suzukiSmoothCoreToL2 v =
        v.1.toLp (2 : ENNReal) (volume : Measure Real) := by
    apply Lp.ext
    filter_upwards [
      (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp,
      SchwartzMap.coeFn_toLp v.1 (2 : ENNReal)
        (volume : Measure Real)] with ξ hleft hright
    exact hleft.trans hright.symm
  have hfourier :
      FourierTransform.fourier (suzukiSmoothCoreToL2 v) =
        (SchwartzMap.fourierTransformCLM Complex v.1).toLp
          (2 : ENNReal) (volume : Measure Real) := by
    rw [hsmoothToLp]
    simpa only [SchwartzMap.fourierTransformCLM_apply] using
      (SchwartzMap.toLp_fourier_eq v.1)
  have hfourierCoe :
      (fun ξ : Real =>
        ((FourierTransform.fourier (suzukiSmoothCoreToL2 v) :
          SuzukiL2) ξ)) =ᵐ[volume]
        SchwartzMap.fourierTransformCLM Complex v.1 := by
    rw [hfourier]
    exact (SchwartzMap.fourierTransformCLM Complex v.1).memLp
      (2 : ENNReal) (volume : Measure Real) |>.coeFn_toLp
  filter_upwards [hfourierCoe] with ξ hξ
  unfold suzukiLogWeightedFourier
  rw [hξ]

theorem norm_sq_suzukiLogWeightedFourierToL2_smoothCore
    {a : Real} (v : SuzukiSmoothCore a) :
    ‖suzukiLogWeightedFourierToL2
        ⟨suzukiSmoothCoreToL2 v,
          suzukiSmoothCoreToL2_mem_logFourierDomain v⟩‖ ^ 2 =
      ∫ ξ : Real, suzukiLogFourierWeight ξ *
        ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2 := by
  let weighted : Real → Complex :=
    suzukiLogWeightedFourier (suzukiSmoothCoreToL2 v)
  have hmem : MemLp weighted (2 : ENNReal) volume :=
    suzukiSmoothCoreToL2_mem_logFourierDomain v
  have hnorm := norm_sq_toLp_eq_integral_norm_sq weighted hmem
  change ‖hmem.toLp weighted‖ ^ 2 = _
  rw [hnorm]
  apply integral_congr_ae
  filter_upwards [suzukiLogWeightedFourier_smoothCore_ae v] with ξ hξ
  dsimp only [weighted]
  rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (suzukiLogFourierWeight_nonneg ξ)]

theorem suzukiLogRadiusEnergy_smoothCore_self_re
    {a : Real} (v : SuzukiSmoothCore a) :
    (suzukiLogRadiusEnergy
      (suzukiSmoothCoreToLogRadiusCompletion v)
      (suzukiSmoothCoreToLogRadiusCompletion v)).re =
        ‖suzukiSmoothCoreToL2 v‖ ^ 2 +
          ∫ ξ : Real, suzukiLogFourierWeight ξ *
            ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2 := by
  let weighted : SuzukiL2 :=
    suzukiLogWeightedFourierToL2
      ⟨suzukiSmoothCoreToL2 v,
        suzukiSmoothCoreToL2_mem_logFourierDomain v⟩
  have hbase :
      (inner Complex (suzukiSmoothCoreToL2 v)
        (suzukiSmoothCoreToL2 v)).re =
          ‖suzukiSmoothCoreToL2 v‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) _
  have hweighted : (inner Complex weighted weighted).re = ‖weighted‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) _
  change
    (inner Complex (suzukiSmoothCoreToL2 v)
        (suzukiSmoothCoreToL2 v) +
      inner Complex weighted weighted).re = _
  rw [Complex.add_re, hbase, hweighted]
  dsimp only [weighted]
  rw [norm_sq_suzukiLogWeightedFourierToL2_smoothCore]

/-- Pointwise decomposition of Suzuki's exact source multiplier into the
closed graph weight, its fixed normalization, and the integrable negative
low-frequency logarithm. -/
theorem suzukiSourceLogFourierWeight_eq_graph_sub_loss
    {ξ : Real} (hξ : ξ ≠ 0) :
    suzukiSourceLogFourierWeight ξ =
      suzukiLogFourierWeight ξ +
        (suzukiSourceLogNormalizationConstant - 1) -
          suzukiLowFrequencyLogLoss ξ := by
  rw [suzukiSourceLogFourierWeight_eq hξ]
  rw [← suzukiPosLog_sub_lowFrequencyLogLoss ξ]
  unfold suzukiLogFourierWeight suzukiSourceLogNormalizationConstant
  ring

/-- Exact diagonal decomposition on the smooth core.  This isolates the only
negative part of the source logarithmic form as an explicitly controlled
low-frequency loss. -/
theorem suzukiSourceLogFourierForm_eq_graphEnergy_sub_loss
    {a : Real} (v : SuzukiSmoothCore a) :
    suzukiSourceLogFourierForm v.1 =
      (suzukiLogRadiusEnergy
        (suzukiSmoothCoreToLogRadiusCompletion v)
        (suzukiSmoothCoreToLogRadiusCompletion v)).re +
          (suzukiSourceLogNormalizationConstant - 2) *
            ‖suzukiSmoothCoreToL2 v‖ ^ 2 -
          suzukiLowFrequencyLogLossForm v.1 := by
  let fourierNormSq : Real → Real := fun ξ =>
    ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2
  have hsource : Integrable (fun ξ : Real =>
      suzukiSourceLogFourierWeight ξ * fourierNormSq ξ) := by
    simpa only [fourierNormSq] using
      integrable_suzukiSourceLogFourierFormIntegrand v.1
  have hgraph : Integrable (fun ξ : Real =>
      suzukiLogFourierWeight ξ * fourierNormSq ξ) := by
    simpa only [fourierNormSq] using
      integrable_suzukiLogFourierWeight_normSq v.1
  have hnorm : Integrable fourierNormSq := by
    exact (SchwartzMap.fourierTransformCLM Complex v.1).memLp
      (2 : ENNReal) volume |>.integrable_norm_pow (by norm_num)
  have hloss : Integrable (fun ξ : Real =>
      suzukiLowFrequencyLogLoss ξ * fourierNormSq ξ) := by
    have hcombined : Integrable (fun ξ : Real =>
        suzukiLogFourierWeight ξ * fourierNormSq ξ +
          (suzukiSourceLogNormalizationConstant - 1) *
            fourierNormSq ξ -
          suzukiSourceLogFourierWeight ξ * fourierNormSq ξ) :=
      (hgraph.add
        (hnorm.const_mul (suzukiSourceLogNormalizationConstant - 1))).sub
          hsource
    apply hcombined.congr
    filter_upwards [volume.ae_ne (0 : Real)] with ξ hξ
    rw [suzukiSourceLogFourierWeight_eq_graph_sub_loss hξ]
    ring
  have hintegrand : (fun ξ : Real =>
      suzukiSourceLogFourierWeight ξ * fourierNormSq ξ) =ᵐ[volume]
      fun ξ : Real =>
        suzukiLogFourierWeight ξ * fourierNormSq ξ +
          (suzukiSourceLogNormalizationConstant - 1) *
            fourierNormSq ξ -
          suzukiLowFrequencyLogLoss ξ * fourierNormSq ξ := by
    filter_upwards [volume.ae_ne (0 : Real)] with ξ hξ
    rw [suzukiSourceLogFourierWeight_eq_graph_sub_loss hξ]
    ring
  have hdecomp : suzukiSourceLogFourierForm v.1 =
      (∫ ξ : Real, suzukiLogFourierWeight ξ * fourierNormSq ξ) +
        (suzukiSourceLogNormalizationConstant - 1) *
          (∫ ξ : Real, fourierNormSq ξ) -
        ∫ ξ : Real,
          suzukiLowFrequencyLogLoss ξ * fourierNormSq ξ := by
    unfold suzukiSourceLogFourierForm
    change (∫ ξ : Real,
      suzukiSourceLogFourierWeight ξ * fourierNormSq ξ) = _
    rw [integral_congr_ae hintegrand]
    calc
      (∫ ξ : Real,
          suzukiLogFourierWeight ξ * fourierNormSq ξ +
            (suzukiSourceLogNormalizationConstant - 1) *
              fourierNormSq ξ -
            suzukiLowFrequencyLogLoss ξ * fourierNormSq ξ) =
          (∫ ξ : Real,
            suzukiLogFourierWeight ξ * fourierNormSq ξ +
              (suzukiSourceLogNormalizationConstant - 1) *
                fourierNormSq ξ) -
            ∫ ξ : Real,
              suzukiLowFrequencyLogLoss ξ * fourierNormSq ξ := by
        exact integral_sub
          (hgraph.add (hnorm.const_mul
            (suzukiSourceLogNormalizationConstant - 1))) hloss
      _ = _ := by
        rw [integral_add hgraph
          (hnorm.const_mul (suzukiSourceLogNormalizationConstant - 1))]
        rw [integral_const_mul]
  rw [hdecomp]
  rw [show (∫ ξ : Real, fourierNormSq ξ) =
      ‖suzukiSmoothCoreToL2 v‖ ^ 2 by
    simpa only [fourierNormSq] using
      integral_normSq_fourier_suzukiSmoothCore v]
  rw [show (∫ ξ : Real,
      suzukiLowFrequencyLogLoss ξ * fourierNormSq ξ) =
        suzukiLowFrequencyLogLossForm v.1 by
    rfl]
  rw [suzukiLogRadiusEnergy_smoothCore_self_re v]
  change
    (∫ ξ : Real, suzukiLogFourierWeight ξ * fourierNormSq ξ) +
          (suzukiSourceLogNormalizationConstant - 1) *
            ‖suzukiSmoothCoreToL2 v‖ ^ 2 -
        suzukiLowFrequencyLogLossForm v.1 =
      ‖suzukiSmoothCoreToL2 v‖ ^ 2 +
          (∫ ξ : Real,
            suzukiLogFourierWeight ξ * fourierNormSq ξ) +
        (suzukiSourceLogNormalizationConstant - 2) *
          ‖suzukiSmoothCoreToL2 v‖ ^ 2 -
        suzukiLowFrequencyLogLossForm v.1
  ring

/-- Radius-dependent shift which compensates both the fixed Fourier
normalization and the worst possible negative low-frequency logarithm on the
radius-`a` core. -/
def suzukiSingularRadiusShift (a : Real) : Real :=
  2 - suzukiSourceLogNormalizationConstant + 4 * a

/-- Shifted exact Fourier-source norm square on the smooth core. -/
def suzukiSourceShiftedCoreNormSq
    {a : Real} (v : SuzukiSmoothCore a) : Real :=
  suzukiSourceLogFourierForm v.1 +
    suzukiSingularRadiusShift a * ‖suzukiSmoothCoreToL2 v‖ ^ 2

/-- Shifted exact physical singular-form norm square on the smooth core. -/
def suzukiSingularShiftedCoreNormSq
    {a : Real} (v : SuzukiSmoothCore a) : Real :=
  suzukiSingularLocalForm a v.1 +
    suzukiSingularRadiusShift a * ‖suzukiSmoothCoreToL2 v‖ ^ 2

/-- The shifted source form is exactly the logarithmic graph energy plus the
radius compensation minus the low-frequency loss. -/
theorem suzukiSourceShiftedCoreNormSq_eq_graphEnergy_sub_loss
    {a : Real} (v : SuzukiSmoothCore a) :
    suzukiSourceShiftedCoreNormSq v =
      (suzukiLogRadiusEnergy
        (suzukiSmoothCoreToLogRadiusCompletion v)
        (suzukiSmoothCoreToLogRadiusCompletion v)).re +
          4 * a * ‖suzukiSmoothCoreToL2 v‖ ^ 2 -
          suzukiLowFrequencyLogLossForm v.1 := by
  unfold suzukiSourceShiftedCoreNormSq suzukiSingularRadiusShift
  rw [suzukiSourceLogFourierForm_eq_graphEnergy_sub_loss v]
  ring

theorem sq_norm_suzukiSmoothCoreToL2_le_logRadiusEnergy
    {a : Real} (v : SuzukiSmoothCore a) :
    ‖suzukiSmoothCoreToL2 v‖ ^ 2 ≤
      (suzukiLogRadiusEnergy
        (suzukiSmoothCoreToLogRadiusCompletion v)
        (suzukiSmoothCoreToLogRadiusCompletion v)).re := by
  rw [suzukiLogRadiusEnergy_smoothCore_self_re v]
  have hweighted : 0 ≤ ∫ ξ : Real,
      suzukiLogFourierWeight ξ *
        ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2 :=
    integral_nonneg fun ξ => mul_nonneg
      (suzukiLogFourierWeight_nonneg ξ) (sq_nonneg _)
  linarith

/-- The shifted exact source norm and the closed graph energy are uniformly
equivalent on every positive-radius smooth core. -/
theorem suzukiSourceShiftedCoreNormSq_comparison
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    let graphEnergy :=
      (suzukiLogRadiusEnergy
        (suzukiSmoothCoreToLogRadiusCompletion v)
        (suzukiSmoothCoreToLogRadiusCompletion v)).re
    graphEnergy ≤ suzukiSourceShiftedCoreNormSq v ∧
      suzukiSourceShiftedCoreNormSq v ≤ (1 + 4 * a) * graphEnergy := by
  dsimp only
  let graphEnergy :=
    (suzukiLogRadiusEnergy
      (suzukiSmoothCoreToLogRadiusCompletion v)
      (suzukiSmoothCoreToLogRadiusCompletion v)).re
  have hnorm : ‖suzukiSmoothCoreToL2 v‖ ^ 2 ≤ graphEnergy := by
    exact sq_norm_suzukiSmoothCoreToL2_le_logRadiusEnergy v
  have hlossNonneg : 0 ≤ suzukiLowFrequencyLogLossForm v.1 :=
    suzukiLowFrequencyLogLossForm_nonneg v.1
  have hlossBound : suzukiLowFrequencyLogLossForm v.1 ≤
      4 * a * ‖suzukiSmoothCoreToL2 v‖ ^ 2 :=
    suzukiLowFrequencyLogLossForm_le ha v
  have hgraphNonneg : 0 ≤ graphEnergy :=
    suzukiLogRadiusEnergy_self_re_nonneg
      (suzukiSmoothCoreToLogRadiusCompletion v)
  rw [suzukiSourceShiftedCoreNormSq_eq_graphEnergy_sub_loss v]
  constructor
  · linarith
  · nlinarith

theorem suzukiSingularShiftedCoreNormSq_eq_source
    {a : Real} (hidentity : SuzukiSingularFourierIdentityAt a)
    (v : SuzukiSmoothCore a) :
    suzukiSingularShiftedCoreNormSq v =
      suzukiSourceShiftedCoreNormSq v := by
  unfold suzukiSingularShiftedCoreNormSq
    suzukiSourceShiftedCoreNormSq
  rw [hidentity v]

/-- Once the exact singular/Fourier identity is supplied, the physical
singular norm has the same explicit two-sided comparison with the closed graph
energy. -/
theorem suzukiSingularShiftedCoreNormSq_comparison
    {a : Real} (ha : 0 < a)
    (hidentity : SuzukiSingularFourierIdentityAt a)
    (v : SuzukiSmoothCore a) :
    let graphEnergy :=
      (suzukiLogRadiusEnergy
        (suzukiSmoothCoreToLogRadiusCompletion v)
        (suzukiSmoothCoreToLogRadiusCompletion v)).re
    graphEnergy ≤ suzukiSingularShiftedCoreNormSq v ∧
      suzukiSingularShiftedCoreNormSq v ≤ (1 + 4 * a) * graphEnergy := by
  rw [suzukiSingularShiftedCoreNormSq_eq_source hidentity v]
  exact suzukiSourceShiftedCoreNormSq_comparison ha v

/-- Difference in the fixed-radius smooth core. -/
def suzukiSmoothCoreSub
    {a : Real} (u v : SuzukiSmoothCore a) : SuzukiSmoothCore a :=
  ⟨u.1 - v.1, by
    intro x hx
    by_cases hu : u.1 x = 0
    · have hv : v.1 x ≠ 0 := by
        intro hv
        apply hx
        simp only [sub_apply, hu, hv, sub_zero]
      exact v.2 hv
    · exact u.2 hu⟩

@[simp]
theorem suzukiSmoothCoreSub_apply
    {a : Real} (u v : SuzukiSmoothCore a) (x : Real) :
    (suzukiSmoothCoreSub u v).1 x = u.1 x - v.1 x :=
  rfl

theorem suzukiSmoothCoreToL2_sub
    {a : Real} (u v : SuzukiSmoothCore a) :
    suzukiSmoothCoreToL2 (suzukiSmoothCoreSub u v) =
      suzukiSmoothCoreToL2 u - suzukiSmoothCoreToL2 v := by
  unfold suzukiSmoothCoreToL2 suzukiSmoothCoreSub
  exact MemLp.toLp_sub
    (u.1.memLp (2 : ENNReal) (volume : Measure Real))
    (v.1.memLp (2 : ENNReal) (volume : Measure Real))

theorem suzukiSmoothCoreToLogGraph_sub
    {a : Real} (u v : SuzukiSmoothCore a) :
    suzukiSmoothCoreToLogGraph (suzukiSmoothCoreSub u v) =
      suzukiSmoothCoreToLogGraph u - suzukiSmoothCoreToLogGraph v := by
  apply Subtype.ext
  apply Prod.ext
  · exact suzukiSmoothCoreToL2_sub u v
  · exact suzukiLogFourierPMap.mem_graph_snd_inj
      (suzukiSmoothCoreToLogGraph (suzukiSmoothCoreSub u v)).2
      (suzukiSmoothCoreToLogGraph u - suzukiSmoothCoreToLogGraph v).2
      (suzukiSmoothCoreToL2_sub u v)

theorem sq_norm_suzukiSmoothCoreToLogGraph_le_logRadiusEnergy
    {a : Real} (v : SuzukiSmoothCore a) :
    ‖suzukiSmoothCoreToLogGraph v‖ ^ 2 ≤
      (suzukiLogRadiusEnergy
        (suzukiSmoothCoreToLogRadiusCompletion v)
        (suzukiSmoothCoreToLogRadiusCompletion v)).re := by
  let base : SuzukiL2 := suzukiSmoothCoreToL2 v
  let weighted : SuzukiL2 :=
    suzukiLogWeightedFourierToL2
      ⟨suzukiSmoothCoreToL2 v,
        suzukiSmoothCoreToL2_mem_logFourierDomain v⟩
  have henergy :
      (suzukiLogRadiusEnergy
        (suzukiSmoothCoreToLogRadiusCompletion v)
        (suzukiSmoothCoreToLogRadiusCompletion v)).re =
          ‖base‖ ^ 2 + ‖weighted‖ ^ 2 := by
    change (inner Complex base base + inner Complex weighted weighted).re = _
    rw [Complex.add_re]
    have hbase : (inner Complex base base).re = ‖base‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := Complex) base
    have hweighted : (inner Complex weighted weighted).re = ‖weighted‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := Complex) weighted
    rw [hbase, hweighted]
  rw [henergy]
  change ‖(base, weighted)‖ ^ 2 ≤ ‖base‖ ^ 2 + ‖weighted‖ ^ 2
  rw [Prod.norm_def]
  rcases max_cases ‖base‖ ‖weighted‖ with ⟨hmax, _⟩ | ⟨hmax, _⟩
  · rw [hmax]
    nlinarith [sq_nonneg ‖weighted‖]
  · rw [hmax]
    nlinarith [sq_nonneg ‖base‖]

theorem logRadiusEnergy_le_two_sq_norm_suzukiSmoothCoreToLogGraph
    {a : Real} (v : SuzukiSmoothCore a) :
    (suzukiLogRadiusEnergy
      (suzukiSmoothCoreToLogRadiusCompletion v)
      (suzukiSmoothCoreToLogRadiusCompletion v)).re ≤
        2 * ‖suzukiSmoothCoreToLogGraph v‖ ^ 2 := by
  let base : SuzukiL2 := suzukiSmoothCoreToL2 v
  let weighted : SuzukiL2 :=
    suzukiLogWeightedFourierToL2
      ⟨suzukiSmoothCoreToL2 v,
        suzukiSmoothCoreToL2_mem_logFourierDomain v⟩
  have henergy :
      (suzukiLogRadiusEnergy
        (suzukiSmoothCoreToLogRadiusCompletion v)
        (suzukiSmoothCoreToLogRadiusCompletion v)).re =
          ‖base‖ ^ 2 + ‖weighted‖ ^ 2 := by
    change (inner Complex base base + inner Complex weighted weighted).re = _
    rw [Complex.add_re]
    have hbase : (inner Complex base base).re = ‖base‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := Complex) base
    have hweighted : (inner Complex weighted weighted).re = ‖weighted‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := Complex) weighted
    rw [hbase, hweighted]
  have hbase : ‖base‖ ≤ ‖(base, weighted)‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hweighted : ‖weighted‖ ≤ ‖(base, weighted)‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  have hbaseSq : ‖base‖ ^ 2 ≤ ‖(base, weighted)‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hbase
  have hweightedSq : ‖weighted‖ ^ 2 ≤ ‖(base, weighted)‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hweighted
  rw [henergy]
  change ‖base‖ ^ 2 + ‖weighted‖ ^ 2 ≤
    2 * ‖(base, weighted)‖ ^ 2
  linarith

/-- Core-level norm equivalence which identifies the completion of the exact
shifted singular form with the already constructed logarithmic graph closure.
The graph closure is concrete inside global `L²`; the estimate is uniform in
the core vector and therefore applies to all core differences. -/
theorem suzukiSingularShiftedCoreNormSq_graphNorm_comparison
    {a : Real} (ha : 0 < a)
    (hidentity : SuzukiSingularFourierIdentityAt a)
    (v : SuzukiSmoothCore a) :
    ‖suzukiSmoothCoreToLogGraph v‖ ^ 2 ≤
        suzukiSingularShiftedCoreNormSq v ∧
      suzukiSingularShiftedCoreNormSq v ≤
        (2 * (1 + 4 * a)) * ‖suzukiSmoothCoreToLogGraph v‖ ^ 2 := by
  obtain ⟨hlower, hupper⟩ :=
    suzukiSingularShiftedCoreNormSq_comparison ha hidentity v
  constructor
  · exact (sq_norm_suzukiSmoothCoreToLogGraph_le_logRadiusEnergy v).trans hlower
  · have hscaled := mul_le_mul_of_nonneg_left
      (logRadiusEnergy_le_two_sq_norm_suzukiSmoothCoreToLogGraph v)
      (by positivity : 0 ≤ 1 + 4 * a)
    exact hupper.trans (by
      convert hscaled using 1
      ring)

theorem dist_suzukiSmoothCoreToLogRadiusCompletion_eq_norm_sub
    {a : Real} (u v : SuzukiSmoothCore a) :
    dist (suzukiSmoothCoreToLogRadiusCompletion u)
        (suzukiSmoothCoreToLogRadiusCompletion v) =
      ‖suzukiSmoothCoreToLogGraph (suzukiSmoothCoreSub u v)‖ := by
  change dist (suzukiSmoothCoreToLogGraph u)
      (suzukiSmoothCoreToLogGraph v) = _
  rw [dist_eq_norm, suzukiSmoothCoreToLogGraph_sub]

/-- Cauchy criterion expressed solely through the exact shifted physical form
on differences of smooth-core functions. -/
def SuzukiSingularShiftedCoreCauchy
    {a : Real} (u : Nat → SuzukiSmoothCore a) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
    suzukiSingularShiftedCoreNormSq
      (suzukiSmoothCoreSub (u m) (u n)) < ε

/-- The exact shifted-singular Cauchy sequences are precisely the Cauchy
sequences of the concrete dense core in `SuzukiLogRadiusCompletion`.  Together
with completeness and dense range, this is the sequence-level identification
of the shifted singular completion inside global `L²`. -/
theorem suzukiSingularShiftedCoreCauchy_iff_logRadiusCompletion
    {a : Real} (ha : 0 < a)
    (hidentity : SuzukiSingularFourierIdentityAt a)
    (u : Nat → SuzukiSmoothCore a) :
    SuzukiSingularShiftedCoreCauchy u ↔
      CauchySeq (fun n => suzukiSmoothCoreToLogRadiusCompletion (u n)) := by
  constructor
  · intro hsingular
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hsingular (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hform := hN m hm n hn
    have hlower :=
      (suzukiSingularShiftedCoreNormSq_graphNorm_comparison ha hidentity
        (suzukiSmoothCoreSub (u m) (u n))).1
    have hsquare :
        ‖suzukiSmoothCoreToLogGraph
          (suzukiSmoothCoreSub (u m) (u n))‖ ^ 2 < ε ^ 2 :=
      lt_of_le_of_lt hlower hform
    rw [dist_suzukiSmoothCoreToLogRadiusCompletion_eq_norm_sub]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsquare
  · intro hgraph
    rw [Metric.cauchySeq_iff] at hgraph
    intro ε hε
    let C : Real := 2 * (1 + 4 * a)
    have hC : 0 < C := by
      dsimp only [C]
      positivity
    let δ : Real := Real.sqrt (ε / C)
    have hratio : 0 < ε / C := div_pos hε hC
    have hδ : 0 < δ := by
      dsimp only [δ]
      exact Real.sqrt_pos.2 hratio
    obtain ⟨N, hN⟩ := hgraph δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist := hN m hm n hn
    rw [dist_suzukiSmoothCoreToLogRadiusCompletion_eq_norm_sub] at hdist
    have hsquare :
        ‖suzukiSmoothCoreToLogGraph
          (suzukiSmoothCoreSub (u m) (u n))‖ ^ 2 < δ ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) hδ.le).2 hdist
    have hδsq : δ ^ 2 = ε / C := by
      dsimp only [δ]
      exact Real.sq_sqrt hratio.le
    rw [hδsq] at hsquare
    have hupper :=
      (suzukiSingularShiftedCoreNormSq_graphNorm_comparison ha hidentity
        (suzukiSmoothCoreSub (u m) (u n))).2
    calc
      suzukiSingularShiftedCoreNormSq
          (suzukiSmoothCoreSub (u m) (u n)) ≤
          C * ‖suzukiSmoothCoreToLogGraph
            (suzukiSmoothCoreSub (u m) (u n))‖ ^ 2 := by
        simpa only [C] using hupper
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hsquare hC
      _ = ε := by field_simp

/-- Concrete completion package delivered to the DF6C consumer: the core is
dense in a complete space, the global `L²` realization is injective, and its
Cauchy sequences are exactly those of the shifted physical singular form. -/
theorem suzukiSingularShiftedCompletion_identification
    {a : Real} (ha : 0 < a)
    (hidentity : SuzukiSingularFourierIdentityAt a) :
    DenseRange (suzukiSmoothCoreToLogRadiusCompletion (r := a)) ∧
      Function.Injective (suzukiLogRadiusCompletionToL2 (r := a)) ∧
      ∀ u : Nat → SuzukiSmoothCore a,
        SuzukiSingularShiftedCoreCauchy u ↔
          CauchySeq
            (fun n => suzukiSmoothCoreToLogRadiusCompletion (u n)) := by
  exact ⟨suzukiSmoothCoreToLogRadiusCompletion_denseRange a,
    suzukiLogRadiusCompletionToL2_injective a,
    suzukiSingularShiftedCoreCauchy_iff_logRadiusCompletion ha hidentity⟩

/-- Explicit `L²` bound for Suzuki's scalar, finite-translation, and exact
`r''` finite-radius remainder. -/
def suzukiRSecondFiniteRadiusBound
    {I : Type*} [DecidableEq I] (s : Finset I) (a scalar : Real)
    (coefficient : I → Real) : Real :=
  abs scalar + Finset.sum s (fun i => 2 * abs (coefficient i)) +
    ‖suzukiRSecondGlobalL2Operator a‖

theorem suzukiRSecondFiniteRadiusBound_nonneg
    {I : Type*} [DecidableEq I] (s : Finset I) (a scalar : Real)
    (coefficient : I → Real) :
    0 ≤ suzukiRSecondFiniteRadiusBound s a scalar coefficient := by
  unfold suzukiRSecondFiniteRadiusBound
  positivity

/-- The complete source form on the smooth core, shifted by the local
singular shift and by the exact bounded-remainder constant. -/
def suzukiRSecondCompleteShiftedCoreNormSq
    {I : Type*} [DecidableEq I] (s : Finset I) {a : Real}
    (scalar : Real) (coefficient shift : I → Real)
    (v : SuzukiSmoothCore a) : Real :=
  suzukiSingularLocalForm a v.1 +
    suzukiRSecondFiniteRadiusRemainder s a scalar coefficient shift
      (suzukiSmoothCoreToL2 v) +
    (suzukiSingularRadiusShift a +
      suzukiRSecondFiniteRadiusBound s a scalar coefficient) *
        ‖suzukiSmoothCoreToL2 v‖ ^ 2

theorem suzukiRSecondCompleteShiftedCoreNormSq_eq
    {I : Type*} [DecidableEq I] (s : Finset I) {a : Real}
    (scalar : Real) (coefficient shift : I → Real)
    (v : SuzukiSmoothCore a) :
    suzukiRSecondCompleteShiftedCoreNormSq
        s scalar coefficient shift v =
      suzukiSingularShiftedCoreNormSq v +
        suzukiRSecondFiniteRadiusRemainder s a scalar coefficient shift
          (suzukiSmoothCoreToL2 v) +
        suzukiRSecondFiniteRadiusBound s a scalar coefficient *
          ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
  unfold suzukiRSecondCompleteShiftedCoreNormSq
    suzukiSingularShiftedCoreNormSq
  ring

/-- The exact complete shifted form and the exact local shifted singular form
have equivalent core norm squares. -/
theorem suzukiRSecondCompleteShiftedCoreNormSq_comparison
    {I : Type*} [DecidableEq I] (s : Finset I) {a : Real}
    (ha : 0 < a) (hidentity : SuzukiSingularFourierIdentityAt a)
    (scalar : Real) (coefficient shift : I → Real)
    (v : SuzukiSmoothCore a) :
    let bound := suzukiRSecondFiniteRadiusBound s a scalar coefficient
    suzukiSingularShiftedCoreNormSq v ≤
        suzukiRSecondCompleteShiftedCoreNormSq
          s scalar coefficient shift v ∧
      suzukiRSecondCompleteShiftedCoreNormSq
          s scalar coefficient shift v ≤
        (1 + 2 * bound) * suzukiSingularShiftedCoreNormSq v := by
  dsimp only
  let bound := suzukiRSecondFiniteRadiusBound s a scalar coefficient
  let remainder :=
    suzukiRSecondFiniteRadiusRemainder s a scalar coefficient shift
      (suzukiSmoothCoreToL2 v)
  have hbound : 0 ≤ bound := by
    exact suzukiRSecondFiniteRadiusBound_nonneg s a scalar coefficient
  have hremainder : |remainder| ≤
      bound * ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
    exact suzukiRSecondFiniteRadiusRemainder_abs_le
      s a scalar coefficient shift (suzukiSmoothCoreToL2 v)
  have hnorm : ‖suzukiSmoothCoreToL2 v‖ ^ 2 ≤
      suzukiSingularShiftedCoreNormSq v := by
    exact (sq_norm_suzukiSmoothCoreToL2_le_logRadiusEnergy v).trans
      (suzukiSingularShiftedCoreNormSq_comparison ha hidentity v).1
  have hscale : 2 * bound * ‖suzukiSmoothCoreToL2 v‖ ^ 2 ≤
      2 * bound * suzukiSingularShiftedCoreNormSq v :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hlower := (abs_le.mp hremainder).1
  have hupper := (abs_le.mp hremainder).2
  rw [suzukiRSecondCompleteShiftedCoreNormSq_eq]
  constructor
  · dsimp only [remainder] at hlower ⊢
    nlinarith
  · dsimp only [remainder] at hupper ⊢
    nlinarith

/-- Direct graph-norm comparison for the exact complete shifted source form.
As with the local estimate, it applies to every core difference. -/
theorem suzukiRSecondCompleteShiftedCoreNormSq_graphNorm_comparison
    {I : Type*} [DecidableEq I] (s : Finset I) {a : Real}
    (ha : 0 < a) (hidentity : SuzukiSingularFourierIdentityAt a)
    (scalar : Real) (coefficient shift : I → Real)
    (v : SuzukiSmoothCore a) :
    let bound := suzukiRSecondFiniteRadiusBound s a scalar coefficient
    ‖suzukiSmoothCoreToLogGraph v‖ ^ 2 ≤
        suzukiRSecondCompleteShiftedCoreNormSq
          s scalar coefficient shift v ∧
      suzukiRSecondCompleteShiftedCoreNormSq
          s scalar coefficient shift v ≤
        ((1 + 2 * bound) * (2 * (1 + 4 * a))) *
          ‖suzukiSmoothCoreToLogGraph v‖ ^ 2 := by
  dsimp only
  let bound := suzukiRSecondFiniteRadiusBound s a scalar coefficient
  obtain ⟨hcompleteLower, hcompleteUpper⟩ :=
    suzukiRSecondCompleteShiftedCoreNormSq_comparison
      s ha hidentity scalar coefficient shift v
  obtain ⟨hgraphLower, hsingularUpper⟩ :=
    suzukiSingularShiftedCoreNormSq_graphNorm_comparison ha hidentity v
  have hbound : 0 ≤ bound :=
    suzukiRSecondFiniteRadiusBound_nonneg s a scalar coefficient
  constructor
  · exact hgraphLower.trans hcompleteLower
  · have hscaled := mul_le_mul_of_nonneg_left hsingularUpper
      (by positivity : 0 ≤ 1 + 2 * bound)
    exact hcompleteUpper.trans (by
      convert hscaled using 1
      ring)

/-- Cauchy criterion for Suzuki's exact complete finite-radius shifted form on
smooth-core differences. -/
def SuzukiRSecondCompleteShiftedCoreCauchy
    {I : Type*} [DecidableEq I] (s : Finset I) {a : Real}
    (scalar : Real) (coefficient shift : I → Real)
    (u : Nat → SuzukiSmoothCore a) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
    suzukiRSecondCompleteShiftedCoreNormSq
      s scalar coefficient shift
        (suzukiSmoothCoreSub (u m) (u n)) < ε

/-- The complete shifted source form has exactly the same completion as the
local shifted singular form and the logarithmic graph closure. -/
theorem suzukiRSecondCompleteShiftedCoreCauchy_iff_logRadiusCompletion
    {I : Type*} [DecidableEq I] (s : Finset I) {a : Real}
    (ha : 0 < a) (hidentity : SuzukiSingularFourierIdentityAt a)
    (scalar : Real) (coefficient shift : I → Real)
    (u : Nat → SuzukiSmoothCore a) :
    SuzukiRSecondCompleteShiftedCoreCauchy
        s scalar coefficient shift u ↔
      CauchySeq (fun n => suzukiSmoothCoreToLogRadiusCompletion (u n)) := by
  constructor
  · intro hcomplete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcomplete (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hform := hN m hm n hn
    have hlower :=
      (suzukiRSecondCompleteShiftedCoreNormSq_graphNorm_comparison
        s ha hidentity scalar coefficient shift
          (suzukiSmoothCoreSub (u m) (u n))).1
    have hsquare :
        ‖suzukiSmoothCoreToLogGraph
          (suzukiSmoothCoreSub (u m) (u n))‖ ^ 2 < ε ^ 2 :=
      lt_of_le_of_lt hlower hform
    rw [dist_suzukiSmoothCoreToLogRadiusCompletion_eq_norm_sub]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsquare
  · intro hgraph
    rw [Metric.cauchySeq_iff] at hgraph
    intro ε hε
    let bound := suzukiRSecondFiniteRadiusBound s a scalar coefficient
    let C : Real := (1 + 2 * bound) * (2 * (1 + 4 * a))
    have hbound : 0 ≤ bound :=
      suzukiRSecondFiniteRadiusBound_nonneg s a scalar coefficient
    have hC : 0 < C := by
      dsimp only [C]
      positivity
    let δ : Real := Real.sqrt (ε / C)
    have hratio : 0 < ε / C := div_pos hε hC
    have hδ : 0 < δ := by
      dsimp only [δ]
      exact Real.sqrt_pos.2 hratio
    obtain ⟨N, hN⟩ := hgraph δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist := hN m hm n hn
    rw [dist_suzukiSmoothCoreToLogRadiusCompletion_eq_norm_sub] at hdist
    have hsquare :
        ‖suzukiSmoothCoreToLogGraph
          (suzukiSmoothCoreSub (u m) (u n))‖ ^ 2 < δ ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) hδ.le).2 hdist
    have hδsq : δ ^ 2 = ε / C := by
      dsimp only [δ]
      exact Real.sq_sqrt hratio.le
    rw [hδsq] at hsquare
    have hupper :=
      (suzukiRSecondCompleteShiftedCoreNormSq_graphNorm_comparison
        s ha hidentity scalar coefficient shift
          (suzukiSmoothCoreSub (u m) (u n))).2
    calc
      suzukiRSecondCompleteShiftedCoreNormSq
          s scalar coefficient shift
            (suzukiSmoothCoreSub (u m) (u n)) ≤
          C * ‖suzukiSmoothCoreToLogGraph
            (suzukiSmoothCoreSub (u m) (u n))‖ ^ 2 := by
        simpa only [C, bound] using hupper
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hsquare hC
      _ = ε := by field_simp

/-- Final local-and-complete completion identification package.  It exposes
the concrete dense complete space, injective global `L²` realization,
support, zero-extension continuity, both exact Cauchy criteria, and joint
continuity of the complete form required by DF6C. -/
theorem suzukiDF6D2_localAndCompleteCompletion_identification
    {I : Type*} [DecidableEq I] (s : Finset I) {a : Real}
    (ha : 0 < a) (hidentity : SuzukiSingularFourierIdentityAt a)
    (scalar : Real) (coefficient shift : I → Real) :
    DenseRange (suzukiSmoothCoreToLogRadiusCompletion (r := a)) ∧
      Function.Injective (suzukiLogRadiusCompletionToL2 (r := a)) ∧
      (∀ v : SuzukiLogRadiusCompletion a,
        suzukiL2SupportedAt a (suzukiLogRadiusCompletionToL2 v)) ∧
      (∀ (b : Real) (hab : a ≤ b),
        Continuous (suzukiLogRadiusCompletionZeroExtension
          (a := a) (b := b) hab)) ∧
      (∀ u : Nat → SuzukiSmoothCore a,
        SuzukiSingularShiftedCoreCauchy u ↔
          CauchySeq
            (fun n => suzukiSmoothCoreToLogRadiusCompletion (u n))) ∧
      (∀ u : Nat → SuzukiSmoothCore a,
        SuzukiRSecondCompleteShiftedCoreCauchy
            s scalar coefficient shift u ↔
          CauchySeq
            (fun n => suzukiSmoothCoreToLogRadiusCompletion (u n))) ∧
      Continuous (Function.uncurry
        (suzukiRSecondLogRadiusCompleteEnergy (a := a)
          s scalar coefficient shift)) := by
  refine ⟨suzukiSmoothCoreToLogRadiusCompletion_denseRange a,
    suzukiLogRadiusCompletionToL2_injective a,
    suzukiLogRadiusCompletionToL2_supportedAt, ?_,
    suzukiSingularShiftedCoreCauchy_iff_logRadiusCompletion ha hidentity,
    suzukiRSecondCompleteShiftedCoreCauchy_iff_logRadiusCompletion
      s ha hidentity scalar coefficient shift,
    suzukiRSecondLogRadiusCompleteEnergy_jointContinuous
      a s scalar coefficient shift⟩
  intro b hab
  exact suzukiLogRadiusCompletionZeroExtension_continuous hab

/-- Compatibility form of the complete DF6D2 package with the classical
scalar identity supplied explicitly. -/
theorem suzukiDF6D2_localAndCompleteCompletion_identification_of_constantIdentity
    (hconstant : SuzukiCosineIntegralConstantIdentity)
    {I : Type*} [DecidableEq I] (s : Finset I) {a : Real}
    (ha : 0 < a) (scalar : Real) (coefficient shift : I → Real) :
    DenseRange (suzukiSmoothCoreToLogRadiusCompletion (r := a)) ∧
      Function.Injective (suzukiLogRadiusCompletionToL2 (r := a)) ∧
      (∀ v : SuzukiLogRadiusCompletion a,
        suzukiL2SupportedAt a (suzukiLogRadiusCompletionToL2 v)) ∧
      (∀ (b : Real) (hab : a ≤ b),
        Continuous (suzukiLogRadiusCompletionZeroExtension
          (a := a) (b := b) hab)) ∧
      (∀ u : Nat → SuzukiSmoothCore a,
        SuzukiSingularShiftedCoreCauchy u ↔
          CauchySeq
            (fun n => suzukiSmoothCoreToLogRadiusCompletion (u n))) ∧
      (∀ u : Nat → SuzukiSmoothCore a,
        SuzukiRSecondCompleteShiftedCoreCauchy
            s scalar coefficient shift u ↔
          CauchySeq
            (fun n => suzukiSmoothCoreToLogRadiusCompletion (u n))) ∧
      Continuous (Function.uncurry
        (suzukiRSecondLogRadiusCompleteEnergy (a := a)
          s scalar coefficient shift)) := by
  exact suzukiDF6D2_localAndCompleteCompletion_identification
    s ha
      (suzukiSingularFourierIdentityAt_of_constantIdentity hconstant ha)
    scalar coefficient shift

/-- The unconditional complete DF6D2 package: the scalar cosine-integral
identity is discharged by the Abel/Frullani calculation. -/
theorem suzukiDF6D2_localAndCompleteCompletion_identification_unconditional
    {I : Type*} [DecidableEq I] (s : Finset I) {a : Real}
    (ha : 0 < a) (scalar : Real) (coefficient shift : I → Real) :
    DenseRange (suzukiSmoothCoreToLogRadiusCompletion (r := a)) ∧
      Function.Injective (suzukiLogRadiusCompletionToL2 (r := a)) ∧
      (∀ v : SuzukiLogRadiusCompletion a,
        suzukiL2SupportedAt a (suzukiLogRadiusCompletionToL2 v)) ∧
      (∀ (b : Real) (hab : a ≤ b),
        Continuous (suzukiLogRadiusCompletionZeroExtension
          (a := a) (b := b) hab)) ∧
      (∀ u : Nat → SuzukiSmoothCore a,
        SuzukiSingularShiftedCoreCauchy u ↔
          CauchySeq
            (fun n => suzukiSmoothCoreToLogRadiusCompletion (u n))) ∧
      (∀ u : Nat → SuzukiSmoothCore a,
        SuzukiRSecondCompleteShiftedCoreCauchy
            s scalar coefficient shift u ↔
          CauchySeq
            (fun n => suzukiSmoothCoreToLogRadiusCompletion (u n))) ∧
      Continuous (Function.uncurry
        (suzukiRSecondLogRadiusCompleteEnergy (a := a)
          s scalar coefficient shift)) := by
  exact
    suzukiDF6D2_localAndCompleteCompletion_identification_of_constantIdentity
      suzukiCosineIntegralConstantIdentity s ha scalar coefficient shift

end

end M100
end Experiments
end RiemannHypothesisProject
