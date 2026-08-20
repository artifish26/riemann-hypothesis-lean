import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaParityFarTargets
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDF0Enclosures
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Corrected closed Suzuki forms for M100-DF6D5B3V

This module constructs the low-frequency logarithmic-loss operator on the
closed logarithmic endpoint completion and uses it to freeze the comparison
form `E` and corrected source complete form `F`.

The old graph-inner-product-plus-remainder form is retained only in a checked
comparison theorem.  It is not used as a surrogate for the corrected source
form.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ComplexConjugate

/-! ## Dense core and low-frequency loss operator -/

/-- The exact smooth-core embedding, bundled linearly into the Hilbert
completion. -/
def suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap (r : Real) :
    SuzukiSmoothCoreLinearSubmodule r →ₗ[Complex]
      SuzukiLogRadiusLinearCompletion r where
  toFun v :=
    ⟨suzukiSmoothCoreToHilbertGraphLinearMap r v,
      subset_closure
        (LinearMap.mem_range_self
          (suzukiSmoothCoreToHilbertGraphLinearMap r) v)⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' c v := by
    apply Subtype.ext
    exact map_smul _ _ _

@[simp]
theorem suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_toL2
    {r : Real} (v : SuzukiSmoothCoreLinearSubmodule r) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v) =
      suzukiSmoothCoreToL2
        (suzukiSmoothCoreLinearSubmoduleAsCore v) :=
  rfl

@[simp]
theorem suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_legacy
    {r : Real} (v : SuzukiSmoothCoreLinearSubmodule r) :
    suzukiLogRadiusLinearCompletionToLegacy
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v) =
      suzukiSmoothCoreToLogRadiusCompletion
        (suzukiSmoothCoreLinearSubmoduleAsCore v) :=
  rfl

theorem suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange
    (r : Real) :
    DenseRange
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r) := by
  have hrange :
      Set.range (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r) =
        Set.range
          (suzukiSmoothCoreToLogRadiusLinearCompletion (r := r)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨suzukiSmoothCoreLinearSubmoduleAsCore v, rfl⟩
    · rintro ⟨v, rfl⟩
      let w : SuzukiSmoothCoreLinearSubmodule r := ⟨v.1, v.2⟩
      exact ⟨w, rfl⟩
  rw [DenseRange, hrange]
  exact suzukiSmoothCoreToLogRadiusLinearCompletion_denseRange r

theorem suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_reflection
    (r : Real) (v : SuzukiSmoothCoreLinearSubmodule r) :
    suzukiLogRadiusLinearReflection r
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v) =
      suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r
        (suzukiSmoothCoreLinearReflection r v) := by
  apply Subtype.ext
  exact suzukiLogHilbertGraphReflection_smoothCore r v

theorem suzukiLowFrequencyLogLoss_neg (ξ : Real) :
    suzukiLowFrequencyLogLoss (-ξ) =
      suzukiLowFrequencyLogLoss ξ := by
  unfold suzukiLowFrequencyLogLoss
  by_cases hξ : ξ ∈ Icc (-1 : Real) 1
  · have hneg : -ξ ∈ Icc (-1 : Real) 1 := by
      constructor <;> linarith [hξ.1, hξ.2]
    rw [Set.indicator_of_mem hneg, Set.indicator_of_mem hξ]
    simp
  · have hneg : -ξ ∉ Icc (-1 : Real) 1 := by
      intro hneg
      apply hξ
      constructor <;> linarith [hneg.1, hneg.2]
    rw [Set.indicator_of_notMem hneg, Set.indicator_of_notMem hξ]

/-- Fourier transform multiplied by the square root of the nonnegative
low-frequency logarithmic loss. -/
def suzukiLowFrequencyWeightedFourier
    {r : Real} (v : SuzukiSmoothCoreLinearSubmodule r) (ξ : Real) : Complex :=
  ((Real.sqrt (suzukiLowFrequencyLogLoss ξ) : Real) : Complex) *
    SchwartzMap.fourierTransformCLM Complex v.1 ξ

theorem suzukiLowFrequencyWeightedFourier_memLp
    {r : Real} (hr : 0 < r)
    (v : SuzukiSmoothCoreLinearSubmodule r) :
    MemLp (suzukiLowFrequencyWeightedFourier v)
      (2 : ENNReal) volume := by
  have hloss : Measurable suzukiLowFrequencyLogLoss := by
    unfold suzukiLowFrequencyLogLoss
    have hlogabs : Measurable (fun ξ : Real => Real.log |ξ|) :=
      Real.measurable_log.comp continuous_abs.measurable
    exact (hlogabs.neg).indicator measurableSet_Icc
  have hmeas : AEStronglyMeasurable
      (suzukiLowFrequencyWeightedFourier v) volume := by
    unfold suzukiLowFrequencyWeightedFourier
    exact
      (Complex.continuous_ofReal.measurable.comp hloss.sqrt).aestronglyMeasurable.mul
        (SchwartzMap.continuous
          (SchwartzMap.fourierTransformCLM Complex v.1)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have h :=
    integrable_suzukiLowFrequencyLogLossFormIntegrand hr
      (suzukiSmoothCoreLinearSubmoduleAsCore v)
  have h' : Integrable (fun ξ : Real =>
      suzukiLowFrequencyLogLoss ξ *
        ‖SchwartzMap.fourierTransformCLM Complex v.1 ξ‖ ^ 2) := by
    simpa only [suzukiSmoothCoreLinearSubmoduleAsCore] using h
  apply h'.congr
  filter_upwards with ξ
  unfold suzukiLowFrequencyWeightedFourier
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (suzukiLowFrequencyLogLoss_nonneg ξ)]

/-- The weighted Fourier transform as a concrete `L²` vector on the smooth
core. -/
def suzukiLowFrequencyWeightedFourierToL2
    {r : Real} (hr : 0 < r)
    (v : SuzukiSmoothCoreLinearSubmodule r) : SuzukiL2 :=
  (suzukiLowFrequencyWeightedFourier_memLp hr v).toLp
    (suzukiLowFrequencyWeightedFourier v)

theorem suzukiLowFrequencyWeightedFourierToL2_add
    {r : Real} (hr : 0 < r)
    (u v : SuzukiSmoothCoreLinearSubmodule r) :
    suzukiLowFrequencyWeightedFourierToL2 hr (u + v) =
      suzukiLowFrequencyWeightedFourierToL2 hr u +
        suzukiLowFrequencyWeightedFourierToL2 hr v := by
  rw [suzukiLowFrequencyWeightedFourierToL2,
    suzukiLowFrequencyWeightedFourierToL2,
    suzukiLowFrequencyWeightedFourierToL2,
    ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards with ξ
  simp [suzukiLowFrequencyWeightedFourier]
  ring

theorem suzukiLowFrequencyWeightedFourierToL2_smul
    {r : Real} (hr : 0 < r) (c : Complex)
    (v : SuzukiSmoothCoreLinearSubmodule r) :
    suzukiLowFrequencyWeightedFourierToL2 hr (c • v) =
      c • suzukiLowFrequencyWeightedFourierToL2 hr v := by
  rw [suzukiLowFrequencyWeightedFourierToL2,
    suzukiLowFrequencyWeightedFourierToL2,
    ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards with ξ
  simp [suzukiLowFrequencyWeightedFourier]
  ring

theorem suzukiLowFrequencyWeightedFourier_reflection
    {r : Real} (v : SuzukiSmoothCoreLinearSubmodule r) (ξ : Real) :
    suzukiLowFrequencyWeightedFourier
        (suzukiSmoothCoreLinearReflection r v) ξ =
      suzukiLowFrequencyWeightedFourier v (-ξ) := by
  have hfourier :=
    congrArg (fun f : SchwartzLineTestFunction => f ξ)
      (fourier_suzukiSchwartzReflection v.1)
  unfold suzukiLowFrequencyWeightedFourier
  rw [suzukiLowFrequencyLogLoss_neg]
  congr 1

theorem suzukiLowFrequencyWeightedFourierToL2_reflection
    {r : Real} (hr : 0 < r)
    (v : SuzukiSmoothCoreLinearSubmodule r) :
    suzukiLowFrequencyWeightedFourierToL2 hr
        (suzukiSmoothCoreLinearReflection r v) =
      suzukiL2Reflection
        (suzukiLowFrequencyWeightedFourierToL2 hr v) := by
  apply Lp.ext
  have hleft :=
    (suzukiLowFrequencyWeightedFourier_memLp hr
      (suzukiSmoothCoreLinearReflection r v)).coeFn_toLp
  have hright :=
    suzukiL2Reflection_coeFn
      (suzukiLowFrequencyWeightedFourierToL2 hr v)
  simp only [suzukiLowFrequencyWeightedFourierToL2] at hright
  have hbase :=
    (Measure.measurePreserving_neg
      (volume : Measure Real)).quasiMeasurePreserving.ae
        ((suzukiLowFrequencyWeightedFourier_memLp hr v).coeFn_toLp)
  filter_upwards [hleft, hright, hbase] with ξ hleft hright hbase
  simp only [suzukiLowFrequencyWeightedFourierToL2]
  rw [hleft, hright, hbase,
    suzukiLowFrequencyWeightedFourier_reflection]

/-- The weighted Fourier transform bundled as a complex-linear map on the
exact smooth core. -/
def suzukiLowFrequencyWeightedFourierLinearMap
    {r : Real} (hr : 0 < r) :
    SuzukiSmoothCoreLinearSubmodule r →ₗ[Complex] SuzukiL2 where
  toFun := suzukiLowFrequencyWeightedFourierToL2 hr
  map_add' := by
    intro u v
    exact suzukiLowFrequencyWeightedFourierToL2_add hr u v
  map_smul' := by
    intro c v
    exact suzukiLowFrequencyWeightedFourierToL2_smul hr c v

theorem norm_sq_suzukiLowFrequencyWeightedFourierLinearMap
    {r : Real} (hr : 0 < r)
    (v : SuzukiSmoothCoreLinearSubmodule r) :
    ‖suzukiLowFrequencyWeightedFourierLinearMap hr v‖ ^ 2 =
      suzukiLowFrequencyLogLossForm v.1 := by
  change ‖suzukiLowFrequencyWeightedFourierToL2 hr v‖ ^ 2 =
    suzukiLowFrequencyLogLossForm v.1
  unfold suzukiLowFrequencyWeightedFourierToL2
  rw [norm_sq_toLp_eq_integral_norm_sq
    (suzukiLowFrequencyWeightedFourier v)
    (suzukiLowFrequencyWeightedFourier_memLp hr v)]
  unfold suzukiLowFrequencyLogLossForm
  apply integral_congr_ae
  filter_upwards with ξ
  unfold suzukiLowFrequencyWeightedFourier
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (suzukiLowFrequencyLogLoss_nonneg ξ)]

theorem suzukiLowFrequencyWeightedFourierLinearMap_bound
    {r : Real} (hr : 0 < r)
    (v : SuzukiSmoothCoreLinearSubmodule r) :
    ‖suzukiLowFrequencyWeightedFourierLinearMap hr v‖ ≤
      (1 + 4 * r) *
        ‖suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v‖ := by
  let w :=
    ‖suzukiLowFrequencyWeightedFourierLinearMap hr v‖
  let g :=
    ‖suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v‖
  have hL2 :
      ‖suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore v)‖ ≤ g := by
    exact suzukiLogRadiusLinearCompletionToL2_norm_le
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v)
  have hsq :
      w ^ 2 ≤ 4 * r *
        ‖suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore v)‖ ^ 2 := by
    rw [norm_sq_suzukiLowFrequencyWeightedFourierLinearMap hr v]
    exact suzukiLowFrequencyLogLossForm_le hr
      (suzukiSmoothCoreLinearSubmoduleAsCore v)
  have hcoefficient : 4 * r ≤ (1 + 4 * r) ^ 2 := by
    nlinarith [sq_nonneg (4 * r)]
  have htargetSq : w ^ 2 ≤ ((1 + 4 * r) * g) ^ 2 := by
    calc
      w ^ 2 ≤ 4 * r *
          ‖suzukiSmoothCoreToL2
            (suzukiSmoothCoreLinearSubmoduleAsCore v)‖ ^ 2 := hsq
      _ ≤ 4 * r * g ^ 2 := by
        gcongr
      _ ≤ (1 + 4 * r) ^ 2 * g ^ 2 := by
        gcongr
      _ = ((1 + 4 * r) * g) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by positivity) (norm_nonneg _))).mp htargetSq

/-- Continuous extension of the weighted Fourier loss map from the dense
smooth core to the full endpoint completion. -/
def suzukiLowFrequencyWeightedFourierCompletionMap
    {r : Real} (hr : 0 < r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex] SuzukiL2 :=
  (suzukiLowFrequencyWeightedFourierLinearMap hr).extendOfNorm
    (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r)

theorem suzukiLowFrequencyWeightedFourierCompletionMap_core
    {r : Real} (hr : 0 < r)
    (v : SuzukiSmoothCoreLinearSubmodule r) :
    suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v) =
      suzukiLowFrequencyWeightedFourierLinearMap hr v := by
  exact LinearMap.extendOfNorm_eq
    (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange r)
    ⟨1 + 4 * r,
      suzukiLowFrequencyWeightedFourierLinearMap_bound hr⟩ v

theorem suzukiLowFrequencyWeightedFourierCompletionMap_reflection
    {r : Real} (hr : 0 < r)
    (u : SuzukiLogRadiusLinearCompletion r) :
    suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiLogRadiusLinearReflection r u) =
      suzukiL2Reflection
        (suzukiLowFrequencyWeightedFourierCompletionMap hr u) := by
  let p : SuzukiLogRadiusLinearCompletion r → Prop := fun w =>
    suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiLogRadiusLinearReflection r w) =
      suzukiL2Reflection
        (suzukiLowFrequencyWeightedFourierCompletionMap hr w)
  apply DenseRange.induction_on
    (p := p)
    (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange r) u
  · exact isClosed_eq
      ((suzukiLowFrequencyWeightedFourierCompletionMap hr).continuous.comp
        (suzukiLogRadiusLinearReflection r).continuous)
      (suzukiL2Reflection.continuous.comp
        (suzukiLowFrequencyWeightedFourierCompletionMap hr).continuous)
  · intro v
    dsimp only [p]
    rw [suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_reflection,
      suzukiLowFrequencyWeightedFourierCompletionMap_core,
      suzukiLowFrequencyWeightedFourierCompletionMap_core]
    exact suzukiLowFrequencyWeightedFourierToL2_reflection hr v

/-- Polarized low-frequency logarithmic loss on the closed completion. -/
def suzukiLowFrequencyLogLossEnergy
    {r : Real} (hr : 0 < r)
    (u v : SuzukiLogRadiusLinearCompletion r) : Complex :=
  inner Complex
    (suzukiLowFrequencyWeightedFourierCompletionMap hr u)
    (suzukiLowFrequencyWeightedFourierCompletionMap hr v)

theorem suzukiLowFrequencyLogLossEnergy_jointContinuous
    {r : Real} (hr : 0 < r) :
    Continuous (Function.uncurry
      (suzukiLowFrequencyLogLossEnergy hr)) := by
  unfold suzukiLowFrequencyLogLossEnergy Function.uncurry
  fun_prop

theorem suzukiLowFrequencyLogLossEnergy_conj_symm
    {r : Real} (hr : 0 < r)
    (u v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLowFrequencyLogLossEnergy hr u v =
      conj (suzukiLowFrequencyLogLossEnergy hr v u) := by
  exact (inner_conj_symm (𝕜 := Complex) _ _).symm

theorem suzukiLowFrequencyLogLossEnergy_reflection
    {r : Real} (hr : 0 < r)
    (u v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLowFrequencyLogLossEnergy hr
        (suzukiLogRadiusLinearReflection r u)
        (suzukiLogRadiusLinearReflection r v) =
      suzukiLowFrequencyLogLossEnergy hr u v := by
  unfold suzukiLowFrequencyLogLossEnergy
  rw [suzukiLowFrequencyWeightedFourierCompletionMap_reflection,
    suzukiLowFrequencyWeightedFourierCompletionMap_reflection,
    suzukiL2Reflection.inner_map_map]

theorem suzukiLowFrequencyLogLossEnergy_core_self_re
    {r : Real} (hr : 0 < r)
    (v : SuzukiSmoothCoreLinearSubmodule r) :
    (suzukiLowFrequencyLogLossEnergy hr
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v)
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap r v)).re =
        suzukiLowFrequencyLogLossForm v.1 := by
  rw [suzukiLowFrequencyLogLossEnergy,
    suzukiLowFrequencyWeightedFourierCompletionMap_core]
  exact (inner_self_eq_norm_sq (𝕜 := Complex)
    (suzukiLowFrequencyWeightedFourierLinearMap hr v)).trans
      (norm_sq_suzukiLowFrequencyWeightedFourierLinearMap hr v)

/-! ## Corrected endpoint forms -/

/-- The full common closed form domain.  The logarithmic endpoint completion
is itself a closed subtype of the Hilbert graph, so no extra predicate is
introduced. -/
abbrev SuzukiYoshidaCorrectedCommonFormDomain : Type :=
  SuzukiLogRadiusLinearCompletion suzukiProjectAStar

/-- The comparison form uses the full common closed domain. -/
abbrev SuzukiYoshidaComparisonFormDomain : Type :=
  SuzukiYoshidaCorrectedCommonFormDomain

/-- The corrected source form uses the same full closed domain. -/
abbrev SuzukiYoshidaCorrectedCompleteFormDomain : Type :=
  SuzukiYoshidaCorrectedCommonFormDomain

theorem suzukiYoshidaComparison_corrected_formDomains_agree :
    SuzukiYoshidaComparisonFormDomain =
      SuzukiYoshidaCorrectedCompleteFormDomain :=
  rfl

/-- The comparison form `E`: graph energy, corrected scalar mass, and the
polarized low-frequency logarithmic loss. -/
def suzukiYoshidaComparisonForm
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) : Complex :=
  inner Complex u v +
    ((suzukiSourceLogNormalizationConstant - 2 : Real) : Complex) *
      inner Complex
        (suzukiLogRadiusLinearCompletionToL2 u)
        (suzukiLogRadiusLinearCompletionToL2 v) -
    suzukiLowFrequencyLogLossEnergy suzukiProjectAStar_pos u v

/-- The signed frozen prime-2 block. -/
def suzukiYoshidaPrimeTwoForm
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) : Complex :=
  suzukiL2FiniteTranslationEnergy
    (suzukiProjectPrimeIndexSet suzukiProjectAStar)
    suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
    (suzukiLogRadiusLinearCompletionToL2 u)
    (suzukiLogRadiusLinearCompletionToL2 v)

/-- The positive-sign gamma remainder.  It is subtracted in the corrected
source form. -/
def suzukiYoshidaGammaRemainderForm
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) : Complex :=
  suzukiL2BoundedOperatorEnergy
    (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
    (suzukiLogRadiusLinearCompletionToL2 u)
    (suzukiLogRadiusLinearCompletionToL2 v)

/-- The corrected closed source complete form
`F = E - s I + P₂ - R_gamma`. -/
def suzukiYoshidaCorrectedCompleteForm
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) : Complex :=
  suzukiYoshidaComparisonForm u v -
    (suzukiSourceLogNormalizationConstant : Complex) *
      inner Complex
        (suzukiLogRadiusLinearCompletionToL2 u)
        (suzukiLogRadiusLinearCompletionToL2 v) +
    suzukiYoshidaPrimeTwoForm u v -
    suzukiYoshidaGammaRemainderForm u v

theorem suzukiSourceLogNormalizationConstant_eq_df0Scalar :
    suzukiSourceLogNormalizationConstant = suzukiDF6D4DF0Scalar := by
  unfold suzukiSourceLogNormalizationConstant suzukiDF6D4DF0Scalar
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) Real.pi_ne_zero]

/-- Explicit signed identity in the exact shape consumed by DF0. -/
theorem suzukiYoshidaCorrectedCompleteForm_eq_signed
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u v =
      suzukiYoshidaComparisonForm u v -
        (suzukiDF6D4DF0Scalar : Complex) *
          inner Complex
            (suzukiLogRadiusLinearCompletionToL2 u)
            (suzukiLogRadiusLinearCompletionToL2 v) +
        suzukiYoshidaPrimeTwoForm u v -
        suzukiYoshidaGammaRemainderForm u v := by
  rw [suzukiYoshidaCorrectedCompleteForm,
    suzukiSourceLogNormalizationConstant_eq_df0Scalar]

/-- Diagonal real form of the signed identity, in the literal shape consumed
by the DF0 comparison theorem. -/
theorem suzukiYoshidaCorrectedCompleteForm_self_re_eq_df0_signed
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    (suzukiYoshidaCorrectedCompleteForm u u).re =
      (suzukiYoshidaComparisonForm u u).re -
        suzukiDF6D4DF0Scalar *
          ‖suzukiLogRadiusLinearCompletionToL2 u‖ ^ 2 +
        (suzukiYoshidaPrimeTwoForm u u).re -
        (suzukiYoshidaGammaRemainderForm u u).re := by
  have hinner :
      (inner Complex
        (suzukiLogRadiusLinearCompletionToL2 u)
        (suzukiLogRadiusLinearCompletionToL2 u)).re =
      ‖suzukiLogRadiusLinearCompletionToL2 u‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) _
  rw [suzukiYoshidaCorrectedCompleteForm_eq_signed,
    Complex.sub_re, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hinner]

/-- Equivalent formula relative to the legacy graph complete form.  This is
the only permitted bridge to that form and makes the correction explicit. -/
theorem suzukiYoshidaCorrectedCompleteForm_eq_old_add_correction
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u v =
      suzukiProjectLogRadiusLinearCompleteEnergy u v +
        ((suzukiSourceLogNormalizationConstant - 2 : Real) : Complex) *
          inner Complex
            (suzukiLogRadiusLinearCompletionToL2 u)
            (suzukiLogRadiusLinearCompletionToL2 v) -
        suzukiLowFrequencyLogLossEnergy suzukiProjectAStar_pos u v := by
  unfold suzukiYoshidaCorrectedCompleteForm
    suzukiYoshidaComparisonForm
    suzukiYoshidaPrimeTwoForm
    suzukiYoshidaGammaRemainderForm
    suzukiProjectLogRadiusLinearCompleteEnergy
    suzukiLogRadiusLinearCompleteEnergy
    suzukiL2FiniteRadiusRemainderEnergy
    suzukiL2BoundedOperatorEnergy
    suzukiRSecondSourceRemainderOperator
    suzukiProjectCompleteScalar
  simp only [ContinuousLinearMap.neg_apply, inner_neg_left,
    Complex.ofReal_neg]
  ring

theorem suzukiYoshidaComparisonForm_jointContinuous :
    Continuous (Function.uncurry suzukiYoshidaComparisonForm) := by
  unfold suzukiYoshidaComparisonForm Function.uncurry
  have hgraph : Continuous
      (fun p :
          SuzukiLogRadiusLinearCompletion suzukiProjectAStar ×
            SuzukiLogRadiusLinearCompletion suzukiProjectAStar =>
        inner Complex p.1 p.2) :=
    continuous_inner
  have hL2 : Continuous
      (fun p :
          SuzukiLogRadiusLinearCompletion suzukiProjectAStar ×
            SuzukiLogRadiusLinearCompletion suzukiProjectAStar =>
        inner Complex
          (suzukiLogRadiusLinearCompletionToL2 p.1)
          (suzukiLogRadiusLinearCompletionToL2 p.2)) :=
    continuous_inner.comp
      ((suzukiLogRadiusLinearCompletionToL2.continuous.comp
          continuous_fst).prodMk
        (suzukiLogRadiusLinearCompletionToL2.continuous.comp
          continuous_snd))
  exact (hgraph.add (continuous_const.mul hL2)).sub
    (suzukiLowFrequencyLogLossEnergy_jointContinuous
      suzukiProjectAStar_pos)

theorem suzukiYoshidaCorrectedCompleteForm_jointContinuous :
    Continuous (Function.uncurry suzukiYoshidaCorrectedCompleteForm) := by
  unfold suzukiYoshidaCorrectedCompleteForm Function.uncurry
  exact (((suzukiYoshidaComparisonForm_jointContinuous.sub
    (continuous_const.mul
      (continuous_inner.comp
        ((suzukiLogRadiusLinearCompletionToL2.continuous.comp
            continuous_fst).prodMk
          (suzukiLogRadiusLinearCompletionToL2.continuous.comp
            continuous_snd))))).add
      ((suzukiL2FiniteTranslationEnergy_jointContinuous
        (suzukiProjectPrimeIndexSet suzukiProjectAStar)
        suzukiProjectPrimeCoefficient suzukiProjectPrimeShift).comp
          ((suzukiLogRadiusLinearCompletionToL2.continuous.comp
              continuous_fst).prodMk
            (suzukiLogRadiusLinearCompletionToL2.continuous.comp
              continuous_snd)))).sub
      ((suzukiL2BoundedOperatorEnergy_jointContinuous
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar)).comp
          ((suzukiLogRadiusLinearCompletionToL2.continuous.comp
              continuous_fst).prodMk
            (suzukiLogRadiusLinearCompletionToL2.continuous.comp
              continuous_snd))))

theorem suzukiYoshidaComparisonForm_conj_symm
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm u v =
      conj (suzukiYoshidaComparisonForm v u) := by
  unfold suzukiYoshidaComparisonForm
  rw [map_sub, map_add, map_mul, Complex.conj_ofReal,
    ← suzukiLowFrequencyLogLossEnergy_conj_symm,
    ← inner_conj_symm (𝕜 := Complex) u v,
    ← inner_conj_symm (𝕜 := Complex)
      (suzukiLogRadiusLinearCompletionToL2 u)
      (suzukiLogRadiusLinearCompletionToL2 v)]

theorem suzukiYoshidaCorrectedCompleteForm_conj_symm
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u v =
      conj (suzukiYoshidaCorrectedCompleteForm v u) := by
  rw [suzukiYoshidaCorrectedCompleteForm_eq_old_add_correction,
    suzukiYoshidaCorrectedCompleteForm_eq_old_add_correction,
    map_sub, map_add, map_mul, Complex.conj_ofReal,
    ← suzukiProjectLogRadiusLinearCompleteEnergy_conj_symm,
    ← suzukiLowFrequencyLogLossEnergy_conj_symm,
    ← inner_conj_symm (𝕜 := Complex)
      (suzukiLogRadiusLinearCompletionToL2 u)
      (suzukiLogRadiusLinearCompletionToL2 v)]

/-! ## Smooth-core normalization -/

theorem suzukiYoshidaComparisonForm_core_self_re
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (suzukiYoshidaComparisonForm
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
        suzukiProjectAStar v)
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
        suzukiProjectAStar v)).re =
      suzukiSourceLogFourierForm v.1 := by
  let core := suzukiSmoothCoreLinearSubmoduleAsCore v
  have hsource :=
    suzukiSourceLogFourierForm_eq_graphEnergy_sub_loss core
  have hL2 :
      (inner Complex
        (suzukiLogRadiusLinearCompletionToL2
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar v))
        (suzukiLogRadiusLinearCompletionToL2
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar v))).re =
        ‖suzukiSmoothCoreToL2 core‖ ^ 2 := by
    rw [suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_toL2]
    exact inner_self_eq_norm_sq (𝕜 := Complex) _
  unfold suzukiYoshidaComparisonForm
  rw [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    suzukiLowFrequencyLogLossEnergy_core_self_re,
    suzukiLogRadiusLinear_inner_eq_legacyEnergy,
    hL2]
  simpa only [
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_toL2,
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_legacy,
    core, suzukiSmoothCoreLinearSubmoduleAsCore] using hsource.symm

set_option maxHeartbeats 800000 in
theorem suzukiYoshidaCorrectedCompleteForm_core_self_re
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (suzukiYoshidaCorrectedCompleteForm
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
        suzukiProjectAStar v)
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
        suzukiProjectAStar v)).re =
      suzukiProjectNormalizedCompleteCoreForm
        (suzukiSmoothCoreLinearSubmoduleAsCore v) := by
  let core := suzukiSmoothCoreLinearSubmoduleAsCore v
  have hidentity :
      suzukiSingularLocalForm suzukiProjectAStar core.1 =
        suzukiSourceLogFourierForm core.1 :=
    suzukiSingularFourierIdentityAt_of_constantIdentity
      suzukiCosineIntegralConstantIdentity suzukiProjectAStar_pos core
  have hcomponents :=
    suzukiProjectNormalizedCompleteCoreForm_eq_groupedComponents core
  have hL2 :
      (inner Complex
        (suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore v))
        (suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore v))).re =
        ‖suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore v)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) _
  have hprime :
      (suzukiL2FiniteTranslationEnergy
        (suzukiProjectPrimeIndexSet suzukiProjectAStar)
        suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
        (suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore v))
        (suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore v))).re =
        suzukiL2FiniteTranslationRemainder
          (suzukiProjectPrimeIndexSet suzukiProjectAStar)
          suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
          (suzukiSmoothCoreToL2
            (suzukiSmoothCoreLinearSubmoduleAsCore v)) :=
    suzukiL2FiniteTranslationEnergy_self_re _ _ _ _
  unfold suzukiYoshidaCorrectedCompleteForm
    suzukiYoshidaPrimeTwoForm
    suzukiYoshidaGammaRemainderForm
  rw [Complex.sub_re, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero,
    suzukiYoshidaComparisonForm_core_self_re]
  simp only [
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_toL2]
  rw [hL2, hprime]
  change
    suzukiSourceLogFourierForm v.1 -
          suzukiSourceLogNormalizationConstant *
            ‖suzukiSmoothCoreToL2 core‖ ^ 2 +
        suzukiL2FiniteTranslationRemainder
          (suzukiProjectPrimeIndexSet suzukiProjectAStar)
          suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
          (suzukiSmoothCoreToL2 core) -
      suzukiL2BoundedOperatorDiagonal
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
        (suzukiSmoothCoreToL2 core) =
      suzukiProjectNormalizedCompleteCoreForm core
  have hidentity_v :
      suzukiSingularLocalForm suzukiProjectAStar core.1 =
        suzukiSourceLogFourierForm v.1 := by
    simpa only [core, suzukiSmoothCoreLinearSubmoduleAsCore] using hidentity
  rw [← hidentity_v]
  rw [hcomponents]
  unfold suzukiProjectCompleteScalar
    suzukiRSecondSourceRemainderOperator
    suzukiL2BoundedOperatorDiagonal
  simp only [ContinuousLinearMap.neg_apply, inner_neg_left,
    Complex.neg_re]
  ring

/-! ## Sesquilinearity and block algebra -/

theorem suzukiLowFrequencyLogLossEnergy_add_left
    {r : Real} (hr : 0 < r)
    (u w v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLowFrequencyLogLossEnergy hr (u + w) v =
      suzukiLowFrequencyLogLossEnergy hr u v +
        suzukiLowFrequencyLogLossEnergy hr w v := by
  simp [suzukiLowFrequencyLogLossEnergy, map_add, inner_add_left]

theorem suzukiLowFrequencyLogLossEnergy_add_right
    {r : Real} (hr : 0 < r)
    (u v w : SuzukiLogRadiusLinearCompletion r) :
    suzukiLowFrequencyLogLossEnergy hr u (v + w) =
      suzukiLowFrequencyLogLossEnergy hr u v +
        suzukiLowFrequencyLogLossEnergy hr u w := by
  simp [suzukiLowFrequencyLogLossEnergy, map_add, inner_add_right]

theorem suzukiLowFrequencyLogLossEnergy_smul_left
    {r : Real} (hr : 0 < r) (c : Complex)
    (u v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLowFrequencyLogLossEnergy hr (c • u) v =
      conj c * suzukiLowFrequencyLogLossEnergy hr u v := by
  simp [suzukiLowFrequencyLogLossEnergy, map_smul, inner_smul_left]

theorem suzukiLowFrequencyLogLossEnergy_smul_right
    {r : Real} (hr : 0 < r) (c : Complex)
    (u v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLowFrequencyLogLossEnergy hr u (c • v) =
      c * suzukiLowFrequencyLogLossEnergy hr u v := by
  simp [suzukiLowFrequencyLogLossEnergy, map_smul, inner_smul_right]

theorem suzukiYoshidaPrimeTwoForm_smul_left
    (c : Complex) (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaPrimeTwoForm (c • u) v =
      conj c * suzukiYoshidaPrimeTwoForm u v := by
  unfold suzukiYoshidaPrimeTwoForm
    suzukiL2FiniteTranslationEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold suzukiL2SymmetricTranslationEnergy
  simp [map_smul, inner_smul_left, inner_smul_right]
  ring

theorem suzukiYoshidaPrimeTwoForm_smul_right
    (c : Complex) (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaPrimeTwoForm u (c • v) =
      c * suzukiYoshidaPrimeTwoForm u v := by
  unfold suzukiYoshidaPrimeTwoForm
    suzukiL2FiniteTranslationEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold suzukiL2SymmetricTranslationEnergy
  simp [map_smul, inner_smul_left, inner_smul_right]
  ring

theorem suzukiYoshidaCorrectedCompleteForm_add_left
    (u w v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm (u + w) v =
      suzukiYoshidaCorrectedCompleteForm u v +
        suzukiYoshidaCorrectedCompleteForm w v := by
  unfold suzukiYoshidaCorrectedCompleteForm
    suzukiYoshidaComparisonForm
    suzukiYoshidaPrimeTwoForm
    suzukiYoshidaGammaRemainderForm
    suzukiL2BoundedOperatorEnergy
  simp [map_add, inner_add_left,
    suzukiLowFrequencyLogLossEnergy_add_left,
    suzukiL2FiniteTranslationEnergy_add_left]
  ring

theorem suzukiYoshidaCorrectedCompleteForm_add_right
    (u v w : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u (v + w) =
      suzukiYoshidaCorrectedCompleteForm u v +
        suzukiYoshidaCorrectedCompleteForm u w := by
  unfold suzukiYoshidaCorrectedCompleteForm
    suzukiYoshidaComparisonForm
    suzukiYoshidaPrimeTwoForm
    suzukiYoshidaGammaRemainderForm
    suzukiL2BoundedOperatorEnergy
  simp [map_add, inner_add_right,
    suzukiLowFrequencyLogLossEnergy_add_right,
    suzukiL2FiniteTranslationEnergy_add_right]
  ring

theorem suzukiYoshidaCorrectedCompleteForm_smul_left
    (c : Complex) (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm (c • u) v =
      conj c * suzukiYoshidaCorrectedCompleteForm u v := by
  unfold suzukiYoshidaCorrectedCompleteForm
    suzukiYoshidaComparisonForm
    suzukiYoshidaGammaRemainderForm
    suzukiL2BoundedOperatorEnergy
  simp [map_smul, inner_smul_left,
    suzukiLowFrequencyLogLossEnergy_smul_left,
    suzukiYoshidaPrimeTwoForm_smul_left]
  ring

theorem suzukiYoshidaCorrectedCompleteForm_smul_right
    (c : Complex) (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u (c • v) =
      c * suzukiYoshidaCorrectedCompleteForm u v := by
  unfold suzukiYoshidaCorrectedCompleteForm
    suzukiYoshidaComparisonForm
    suzukiYoshidaGammaRemainderForm
    suzukiL2BoundedOperatorEnergy
  simp [map_smul, inner_smul_right,
    suzukiLowFrequencyLogLossEnergy_smul_right,
    suzukiYoshidaPrimeTwoForm_smul_right]
  ring

theorem suzukiYoshidaCorrectedCompleteForm_neg_left
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm (-u) v =
      -suzukiYoshidaCorrectedCompleteForm u v := by
  rw [← neg_one_smul Complex u,
    suzukiYoshidaCorrectedCompleteForm_smul_left]
  simp

theorem suzukiYoshidaCorrectedCompleteForm_neg_right
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u (-v) =
      -suzukiYoshidaCorrectedCompleteForm u v := by
  rw [← neg_one_smul Complex v,
    suzukiYoshidaCorrectedCompleteForm_smul_right]
  simp

theorem suzukiYoshidaCorrectedCompleteForm_eq_polarization
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u v =
      (4 : Complex)⁻¹ *
        (suzukiYoshidaCorrectedCompleteForm (u + v) (u + v) -
          suzukiYoshidaCorrectedCompleteForm (u - v) (u - v) -
          Complex.I *
            suzukiYoshidaCorrectedCompleteForm
              (u + Complex.I • v) (u + Complex.I • v) +
          Complex.I *
            suzukiYoshidaCorrectedCompleteForm
              (u - Complex.I • v) (u - Complex.I • v)) := by
  simp [sub_eq_add_neg,
    suzukiYoshidaCorrectedCompleteForm_add_left,
    suzukiYoshidaCorrectedCompleteForm_add_right,
    suzukiYoshidaCorrectedCompleteForm_neg_left,
    suzukiYoshidaCorrectedCompleteForm_neg_right,
    suzukiYoshidaCorrectedCompleteForm_smul_left,
    suzukiYoshidaCorrectedCompleteForm_smul_right]
  ring_nf
  simp [Complex.I_sq] <;> ring

/-- Complex polarization of the checked project-normalized smooth-core
quadratic form.  This is independent of the closed corrected form. -/
def suzukiProjectNormalizedCompleteCorePolarizedForm
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) : Complex :=
  (4 : Complex)⁻¹ *
    ((suzukiProjectNormalizedCompleteCoreForm
        (suzukiSmoothCoreLinearSubmoduleAsCore (u + v)) : Complex) -
      (suzukiProjectNormalizedCompleteCoreForm
        (suzukiSmoothCoreLinearSubmoduleAsCore (u - v)) : Complex) -
      Complex.I *
        (suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore
            (u + Complex.I • v)) : Complex) +
      Complex.I *
        (suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore
            (u - Complex.I • v)) : Complex))

theorem suzukiYoshidaCorrectedCompleteForm_core_self
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) =
      (suzukiProjectNormalizedCompleteCoreForm
        (suzukiSmoothCoreLinearSubmoduleAsCore v) : Complex) := by
  apply Complex.ext
  · exact suzukiYoshidaCorrectedCompleteForm_core_self_re v
  · have hsym :=
      suzukiYoshidaCorrectedCompleteForm_conj_symm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v)
    have him := congrArg Complex.im hsym
    rw [Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

theorem suzukiYoshidaCorrectedCompleteForm_core_polarized
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) =
      suzukiProjectNormalizedCompleteCorePolarizedForm u v := by
  have hplus :=
    suzukiYoshidaCorrectedCompleteForm_core_self (u + v)
  have hminus :=
    suzukiYoshidaCorrectedCompleteForm_core_self (u - v)
  have hiPlus :=
    suzukiYoshidaCorrectedCompleteForm_core_self
      (u + Complex.I • v)
  have hiMinus :=
    suzukiYoshidaCorrectedCompleteForm_core_self
      (u - Complex.I • v)
  simp only [map_add] at hplus
  simp only [map_sub] at hminus
  simp only [map_add, map_smul] at hiPlus
  simp only [map_sub, map_smul] at hiMinus
  rw [suzukiYoshidaCorrectedCompleteForm_eq_polarization]
  unfold suzukiProjectNormalizedCompleteCorePolarizedForm
  rw [hplus, hminus, hiPlus, hiMinus]

/-! ## Reflection and parity -/

theorem suzukiYoshidaComparisonForm_reflection
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm
        (suzukiLogRadiusLinearReflection suzukiProjectAStar u)
        (suzukiLogRadiusLinearReflection suzukiProjectAStar v) =
      suzukiYoshidaComparisonForm u v := by
  unfold suzukiYoshidaComparisonForm
  rw [suzukiLogRadiusLinearReflection_inner_map_map,
    suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiL2Reflection.inner_map_map,
    suzukiLowFrequencyLogLossEnergy_reflection]

theorem suzukiYoshidaPrimeTwoForm_reflection
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaPrimeTwoForm
        (suzukiLogRadiusLinearReflection suzukiProjectAStar u)
        (suzukiLogRadiusLinearReflection suzukiProjectAStar v) =
      suzukiYoshidaPrimeTwoForm u v := by
  unfold suzukiYoshidaPrimeTwoForm
  rw [suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiL2FiniteTranslationEnergy_reflection]

theorem suzukiYoshidaGammaRemainderForm_reflection
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaGammaRemainderForm
        (suzukiLogRadiusLinearReflection suzukiProjectAStar u)
        (suzukiLogRadiusLinearReflection suzukiProjectAStar v) =
      suzukiYoshidaGammaRemainderForm u v := by
  unfold suzukiYoshidaGammaRemainderForm
    suzukiL2BoundedOperatorEnergy
  rw [suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiRSecondGlobalL2Operator_reflection,
    suzukiL2Reflection.inner_map_map]

set_option maxHeartbeats 800000 in
theorem suzukiYoshidaCorrectedCompleteForm_reflection
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiLogRadiusLinearReflection suzukiProjectAStar u)
        (suzukiLogRadiusLinearReflection suzukiProjectAStar v) =
      suzukiYoshidaCorrectedCompleteForm u v := by
  unfold suzukiYoshidaCorrectedCompleteForm
  rw [suzukiYoshidaComparisonForm_reflection,
    suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiL2Reflection.inner_map_map,
    suzukiYoshidaPrimeTwoForm_reflection,
    suzukiYoshidaGammaRemainderForm_reflection]

theorem suzukiYoshidaCorrectedCompleteForm_even_odd_split
    (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm v v =
      suzukiYoshidaCorrectedCompleteForm
          (suzukiLogRadiusLinearEvenProjector suzukiProjectAStar v)
          (suzukiLogRadiusLinearEvenProjector suzukiProjectAStar v) +
        suzukiYoshidaCorrectedCompleteForm
          (suzukiLogRadiusLinearOddProjector suzukiProjectAStar v)
          (suzukiLogRadiusLinearOddProjector suzukiProjectAStar v) := by
  let e := suzukiLogRadiusLinearEvenProjector suzukiProjectAStar v
  let o := suzukiLogRadiusLinearOddProjector suzukiProjectAStar v
  have he :
      suzukiLogRadiusLinearReflection suzukiProjectAStar e = e :=
    suzukiLogRadiusLinearEvenProjector_reflection suzukiProjectAStar v
  have ho :
      suzukiLogRadiusLinearReflection suzukiProjectAStar o = -o :=
    suzukiLogRadiusLinearOddProjector_reflection suzukiProjectAStar v
  have hcrossEO :=
    suzukiYoshidaCorrectedCompleteForm_reflection e o
  rw [he, ho, suzukiYoshidaCorrectedCompleteForm_neg_right] at hcrossEO
  have hcrossEOzero :
      suzukiYoshidaCorrectedCompleteForm e o = 0 :=
    CharZero.neg_eq_self_iff.mp hcrossEO
  have hcrossOE :=
    suzukiYoshidaCorrectedCompleteForm_reflection o e
  rw [he, ho, suzukiYoshidaCorrectedCompleteForm_neg_left] at hcrossOE
  have hcrossOEzero :
      suzukiYoshidaCorrectedCompleteForm o e = 0 :=
    CharZero.neg_eq_self_iff.mp hcrossOE
  have hv : e + o = v :=
    suzukiLogRadiusLinearEvenProjector_add_oddProjector
      suzukiProjectAStar v
  calc
    suzukiYoshidaCorrectedCompleteForm v v =
        suzukiYoshidaCorrectedCompleteForm (e + o) (e + o) := by
          rw [hv]
    _ = (suzukiYoshidaCorrectedCompleteForm e e +
          suzukiYoshidaCorrectedCompleteForm e o) +
        (suzukiYoshidaCorrectedCompleteForm o e +
          suzukiYoshidaCorrectedCompleteForm o o) := by
          rw [suzukiYoshidaCorrectedCompleteForm_add_left,
            suzukiYoshidaCorrectedCompleteForm_add_right,
            suzukiYoshidaCorrectedCompleteForm_add_right]
    _ = suzukiYoshidaCorrectedCompleteForm e e +
        suzukiYoshidaCorrectedCompleteForm o o := by
          rw [hcrossEOzero, hcrossOEzero]
          ring

/-- Exact low/cross/far expansion for the corrected source form. -/
theorem suzukiYoshidaCorrectedCompleteForm_block
    (low far : SuzukiYoshidaCorrectedCommonFormDomain) :
    (suzukiYoshidaCorrectedCompleteForm
        (low + far) (low + far)).re =
      (suzukiYoshidaCorrectedCompleteForm low low).re +
        2 * (suzukiYoshidaCorrectedCompleteForm low far).re +
        (suzukiYoshidaCorrectedCompleteForm far far).re := by
  rw [suzukiYoshidaCorrectedCompleteForm_add_left,
    suzukiYoshidaCorrectedCompleteForm_add_right,
    suzukiYoshidaCorrectedCompleteForm_add_right,
    suzukiYoshidaCorrectedCompleteForm_conj_symm far low]
  simp only [Complex.add_re, Complex.conj_re]
  ring

end

end RiemannHypothesisProject.Experiments.M100
