import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAdjointDomain

/-!
# M100-DF6F smooth-core Fourier domains

This module discharges the two elementary weighted Fourier-domain conditions
left visible by the source adjoint-domain reduction.  The high-frequency
condition follows from Schwartz decay and the existing polynomial majorant
for the logarithmic weight.  The low-frequency condition follows from local
square-integrability of the logarithmic loss and boundedness of a Schwartz
Fourier transform on its compact support.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set
open scoped ENNReal

/-- Multiplication of a Schwartz function by one full Suzuki logarithmic
weight is square-integrable. -/
theorem schwartz_memLp_suzukiExtraLogWeighted
    (f : SchwartzLineTestFunction) :
    MemLp
      (fun xi : Real => (suzukiLogFourierWeight xi : Complex) * f xi)
      (2 : ENNReal) (volume : Measure Real) := by
  let polynomialMultiplier : SchwartzLineTestFunction :=
    SchwartzMap.smulLeftCLM Complex
      (fun xi : Real => (2 + xi ^ 2) ^ 2) f
  have hgrowth :
      Function.HasTemperateGrowth (fun xi : Real => (2 + xi ^ 2) ^ 2) := by
    fun_prop
  have hpolynomial :
      MemLp (polynomialMultiplier : Real → Complex)
        (2 : ENNReal) (volume : Measure Real) :=
    polynomialMultiplier.memLp
      (2 : ENNReal) (volume : Measure Real)
  apply hpolynomial.mono
  · exact
      ((Complex.continuous_ofReal.comp
          continuous_suzukiLogFourierWeight).mul
        f.continuous).aestronglyMeasurable
  · filter_upwards with xi
    rw [show polynomialMultiplier xi =
        ((((2 + xi ^ 2) ^ 2 : Real) : Complex) * f xi) by
      simpa only [polynomialMultiplier, Complex.real_smul] using
        SchwartzMap.smulLeftCLM_apply_apply hgrowth f xi]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (suzukiLogFourierWeight_nonneg xi),
      abs_of_nonneg (sq_nonneg (2 + xi ^ 2))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg (f xi))
    have hsqrt := sqrt_suzukiLogFourierWeight_le_quadratic xi
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
      (by positivity : 0 ≤ (2 + xi ^ 2 : Real))).2 hsqrt
    simpa [Real.sq_sqrt (suzukiLogFourierWeight_nonneg xi)] using hsq

/-- A smooth Suzuki core vector belongs to the one-extra-log domain. -/
theorem suzukiSmoothCoreToL2_mem_extraLogFourierDomain
    {r : Real} (v : SuzukiSmoothCore r) :
    SuzukiExtraLogFourierDomain (suzukiSmoothCoreToL2 v) := by
  let f : SchwartzLineTestFunction :=
    SchwartzMap.fourierTransformCLM Complex v.1
  have hf := schwartz_memLp_suzukiExtraLogWeighted f
  unfold SuzukiExtraLogFourierDomain suzukiExtraLogWeightedFourier
  apply hf.ae_eq
  filter_upwards [fourier_suzukiSmoothCoreToL2_coe_ae v] with xi hxi
  rw [hxi]
  simp only [f, SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.fourier_coe]

/-- Multiplication of a Schwartz function by the compactly supported
low-frequency logarithmic loss is square-integrable. -/
theorem schwartz_memLp_suzukiLowLossExtraWeighted
    (f : SchwartzLineTestFunction) :
    MemLp
      (fun xi : Real => (suzukiLowFrequencyLogLoss xi : Complex) * f xi)
      (2 : ENNReal) (volume : Measure Real) := by
  let ordinary : Real → Complex := fun xi =>
    (suzukiLowFrequencyLogLoss xi : Complex) * f xi
  have hloss : Measurable suzukiLowFrequencyLogLoss := by
    unfold suzukiLowFrequencyLogLoss
    have hlogabs : Measurable (fun xi : Real => Real.log |xi|) :=
      Real.measurable_log.comp continuous_abs.measurable
    exact hlogabs.neg.indicator measurableSet_Icc
  have hmeas : AEStronglyMeasurable ordinary volume :=
    ((Complex.continuous_ofReal.measurable.comp hloss).mul
      f.continuous.measurable).aestronglyMeasurable
  have hlossOn : IntegrableOn
      (fun xi : Real => suzukiLowFrequencyLogLoss xi ^ 2)
      (Icc (-1 : Real) 1) :=
    integrable_suzukiLowFrequencyLogLoss_sq.integrableOn
  have hproduct : IntegrableOn (fun xi : Real =>
      suzukiLowFrequencyLogLoss xi ^ 2 * ‖f xi‖ ^ 2)
      (Icc (-1 : Real) 1) :=
    hlossOn.mul_continuousOn
      ((f.continuous.norm.pow 2).continuousOn) isCompact_Icc
  have hindicator := hproduct.integrable_indicator measurableSet_Icc
  have hint : Integrable (fun xi : Real => ‖ordinary xi‖ ^ 2) := by
    apply hindicator.congr
    filter_upwards with xi
    by_cases hxi : xi ∈ Icc (-1 : Real) 1
    · simp only [indicator_of_mem hxi]
      dsimp only [ordinary]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (suzukiLowFrequencyLogLoss_nonneg xi), mul_pow]
    · rw [indicator_of_notMem hxi]
      have hlossZero : suzukiLowFrequencyLogLoss xi = 0 := by
        unfold suzukiLowFrequencyLogLoss
        rw [indicator_of_notMem hxi]
      simp [ordinary, hlossZero]
  apply (integrable_norm_rpow_iff hmeas (by norm_num) (by simp)).mp
  simpa [ordinary] using hint

/-- A smooth Suzuki core vector belongs to the additional low-frequency-loss
domain. -/
theorem suzukiSmoothCoreToL2_mem_lowLossExtraFourierDomain
    {r : Real} (v : SuzukiSmoothCore r) :
    SuzukiLowLossExtraFourierDomain (suzukiSmoothCoreToL2 v) := by
  let f : SchwartzLineTestFunction :=
    SchwartzMap.fourierTransformCLM Complex v.1
  have hf := schwartz_memLp_suzukiLowLossExtraWeighted f
  unfold SuzukiLowLossExtraFourierDomain
    suzukiLowLossExtraWeightedFourier
  apply hf.ae_eq
  filter_upwards [fourier_suzukiSmoothCoreToL2_coe_ae v] with xi hxi
  rw [hxi]
  simp only [f, SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.fourier_coe]

/-- Both corrected-form ambient domains hold automatically on every smooth
primitive core. -/
theorem suzukiSmoothCoreCorrectedAmbientDomains
    (a : Real) : SuzukiSmoothCoreCorrectedAmbientDomainsAt a := by
  intro u
  rw [suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_toL2]
  exact ⟨
    suzukiSmoothCoreToL2_mem_extraLogFourierDomain
      (suzukiSmoothCoreLinearSubmoduleAsCore u),
    suzukiSmoothCoreToL2_mem_lowLossExtraFourierDomain
      (suzukiSmoothCoreLinearSubmoduleAsCore u)⟩

/-- Equation (2.5) alone now supplies the source-side maximal-adjoint-domain
condition; the two Fourier-domain side conditions are automatic on the
smooth primitive core. -/
theorem suzukiSourceGDifferentialInAdjointDomainAt_of_source
    (hsource : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiSourceGDifferentialInAdjointDomainAt
      suzukiProjectAStar suzukiProjectAStar_pos :=
  suzukiSourceGDifferentialInAdjointDomainAt_of_ambientDomains hsource
    (suzukiSmoothCoreCorrectedAmbientDomains suzukiProjectAStar)

end

end RiemannHypothesisProject.Experiments.M100
