import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaPrimeTranslationEntries
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDirichletIntegral

/-!
# Ordered comparison entries for the B3Q-G source evaluation

This module separates the remaining analytic comparison-form calculation from
the already checked DF6D4 normalization.  The source-side transform is the
singular sine integral for positive modes.  Its zero-mode branch is kept
explicit because the constant even mode uses the endpoint convention already
frozen in DF6D4 rather than the positive-mode Dirichlet integral.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory
open scoped ComplexConjugate Topology

/-! ## Closed comparison form and smooth-core polarization -/

theorem suzukiYoshidaComparisonForm_add_left
    (u w v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm (u + w) v =
      suzukiYoshidaComparisonForm u v +
        suzukiYoshidaComparisonForm w v := by
  unfold suzukiYoshidaComparisonForm
  simp [map_add, inner_add_left,
    suzukiLowFrequencyLogLossEnergy_add_left]
  ring

theorem suzukiYoshidaComparisonForm_add_right
    (u v w : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm u (v + w) =
      suzukiYoshidaComparisonForm u v +
        suzukiYoshidaComparisonForm u w := by
  unfold suzukiYoshidaComparisonForm
  simp [map_add, inner_add_right,
    suzukiLowFrequencyLogLossEnergy_add_right]
  ring

theorem suzukiYoshidaComparisonForm_smul_left
    (c : Complex) (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm (c • u) v =
      conj c * suzukiYoshidaComparisonForm u v := by
  unfold suzukiYoshidaComparisonForm
  simp [map_smul, inner_smul_left,
    suzukiLowFrequencyLogLossEnergy_smul_left]
  ring

theorem suzukiYoshidaComparisonForm_smul_right
    (c : Complex) (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm u (c • v) =
      c * suzukiYoshidaComparisonForm u v := by
  unfold suzukiYoshidaComparisonForm
  simp [map_smul, inner_smul_right,
    suzukiLowFrequencyLogLossEnergy_smul_right]
  ring

theorem suzukiYoshidaComparisonForm_sub_left
    (u w v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm (u - w) v =
      suzukiYoshidaComparisonForm u v -
        suzukiYoshidaComparisonForm w v := by
  rw [sub_eq_add_neg, suzukiYoshidaComparisonForm_add_left]
  rw [show -w = (-1 : Complex) • w by
      exact (neg_one_smul Complex w).symm,
    suzukiYoshidaComparisonForm_smul_left]
  rw [sub_eq_add_neg]
  norm_num

theorem suzukiYoshidaComparisonForm_sub_right
    (u v w : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm u (v - w) =
      suzukiYoshidaComparisonForm u v -
        suzukiYoshidaComparisonForm u w := by
  rw [sub_eq_add_neg, suzukiYoshidaComparisonForm_add_right]
  rw [show -w = (-1 : Complex) • w by
      exact (neg_one_smul Complex w).symm,
    suzukiYoshidaComparisonForm_smul_right]
  rw [sub_eq_add_neg]
  norm_num

theorem suzukiYoshidaComparisonForm_neg_left
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm (-u) v =
      -suzukiYoshidaComparisonForm u v := by
  rw [← neg_one_smul Complex u,
    suzukiYoshidaComparisonForm_smul_left]
  simp

theorem suzukiYoshidaComparisonForm_neg_right
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm u (-v) =
      -suzukiYoshidaComparisonForm u v := by
  rw [← neg_one_smul Complex v,
    suzukiYoshidaComparisonForm_smul_right]
  simp

theorem suzukiYoshidaComparisonForm_eq_polarization
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm u v =
      (4 : Complex)⁻¹ *
        (suzukiYoshidaComparisonForm (u + v) (u + v) -
          suzukiYoshidaComparisonForm (u - v) (u - v) -
          Complex.I *
            suzukiYoshidaComparisonForm
              (u + Complex.I • v) (u + Complex.I • v) +
          Complex.I *
            suzukiYoshidaComparisonForm
              (u - Complex.I • v) (u - Complex.I • v)) := by
  simp [sub_eq_add_neg,
    suzukiYoshidaComparisonForm_add_left,
    suzukiYoshidaComparisonForm_add_right,
    suzukiYoshidaComparisonForm_neg_left,
    suzukiYoshidaComparisonForm_neg_right,
    suzukiYoshidaComparisonForm_smul_left,
    suzukiYoshidaComparisonForm_smul_right]
  ring_nf
  simp [Complex.I_sq] <;> ring

/-! ## Source Fourier polarization convention -/

/-- The pointwise integrand of Suzuki's complex-polarized logarithmic Fourier
form.  Naming it makes the argument-order conversion at the comparison-form
boundary explicit. -/
def suzukiSourceLogFourierPolarizedIntegrand
    (u v : SchwartzLineTestFunction) (xi : Real) : Complex :=
  ((suzukiSourceLogFourierWeight xi : Real) : Complex) *
    (SchwartzMap.fourierTransformCLM Complex u xi *
      conj (SchwartzMap.fourierTransformCLM Complex v xi))

theorem suzukiSourceLogFourierPolarizedIntegrand_reverse_eq_polarization
    (u v : SchwartzLineTestFunction) (xi : Real) :
    suzukiSourceLogFourierPolarizedIntegrand v u xi =
      (4 : Complex)⁻¹ *
        (suzukiSourceLogFourierPolarizedIntegrand (u + v) (u + v) xi -
          suzukiSourceLogFourierPolarizedIntegrand (u - v) (u - v) xi -
          Complex.I *
            suzukiSourceLogFourierPolarizedIntegrand
              (u + Complex.I • v) (u + Complex.I • v) xi +
          Complex.I *
            suzukiSourceLogFourierPolarizedIntegrand
              (u - Complex.I • v) (u - Complex.I • v) xi) := by
  simp [suzukiSourceLogFourierPolarizedIntegrand, map_add, map_sub, map_smul]
  ring_nf
  simp [Complex.I_sq] <;> ring

/-- Every cross integrand in Suzuki's complex-polarized logarithmic Fourier
form is integrable. -/
theorem integrable_suzukiSourceLogFourierPolarizedIntegrand
    (u v : SchwartzLineTestFunction) :
    Integrable (suzukiSourceLogFourierPolarizedIntegrand u v) := by
  let p : SchwartzLineTestFunction := v + u
  let q : SchwartzLineTestFunction := v - u
  let r : SchwartzLineTestFunction := v + Complex.I • u
  let s : SchwartzLineTestFunction := v - Complex.I • u
  have hp := integrable_suzukiSourceLogFourierPolarizedSelfIntegrand p
  have hq := integrable_suzukiSourceLogFourierPolarizedSelfIntegrand q
  have hr := integrable_suzukiSourceLogFourierPolarizedSelfIntegrand r
  have hs := integrable_suzukiSourceLogFourierPolarizedSelfIntegrand s
  have hcomb : Integrable
      (fun xi : Real =>
        (4 : Complex)⁻¹ *
          (suzukiSourceLogFourierPolarizedIntegrand p p xi -
            suzukiSourceLogFourierPolarizedIntegrand q q xi -
            Complex.I *
              suzukiSourceLogFourierPolarizedIntegrand r r xi +
            Complex.I *
              suzukiSourceLogFourierPolarizedIntegrand s s xi)) := by
    apply Integrable.const_mul
    exact (((hp.sub hq).sub (hr.const_mul Complex.I)).add
      (hs.const_mul Complex.I))
  apply hcomb.congr
  filter_upwards with xi
  simpa [p, q, r, s] using
    (suzukiSourceLogFourierPolarizedIntegrand_reverse_eq_polarization
      v u xi).symm

/-- The diagonal complex-polarized source form is the complexification of the
real source quadratic form. -/
theorem suzukiSourceLogFourierPolarizedForm_self
    (v : SchwartzLineTestFunction) :
    suzukiSourceLogFourierPolarizedForm v v =
      (suzukiSourceLogFourierForm v : Complex) := by
  apply Complex.ext
  · exact suzukiSourceLogFourierPolarizedForm_self_re v
  · have hint :=
      integrable_suzukiSourceLogFourierPolarizedSelfIntegrand v
    unfold suzukiSourceLogFourierPolarizedForm
    simp only [Complex.ofReal_im]
    calc
      (∫ xi : Real,
          ((suzukiSourceLogFourierWeight xi : Real) : Complex) *
            (SchwartzMap.fourierTransformCLM Complex v xi *
              conj (SchwartzMap.fourierTransformCLM Complex v xi))).im =
          ∫ xi : Real,
            (((suzukiSourceLogFourierWeight xi : Real) : Complex) *
              (SchwartzMap.fourierTransformCLM Complex v xi *
                conj (SchwartzMap.fourierTransformCLM Complex v xi))).im :=
        (integral_im hint).symm
      _ = 0 := by
        have hzero :
            (fun xi : Real =>
              (((suzukiSourceLogFourierWeight xi : Real) : Complex) *
                (SchwartzMap.fourierTransformCLM Complex v xi *
                  conj (SchwartzMap.fourierTransformCLM Complex v xi))).im) =
              (0 : Real → Real) := by
          funext xi
          rw [Complex.mul_conj']
          norm_cast
        rw [hzero]
        simp

/-- Suzuki's weighted Fourier form uses the opposite argument order from the
comparison form.  After reversing the arguments, its integral is exactly the
project's four-diagonal polarization convention. -/
theorem suzukiSourceLogFourierPolarizedForm_reverse_eq_polarization
    (u v : SchwartzLineTestFunction) :
    suzukiSourceLogFourierPolarizedForm v u =
      (4 : Complex)⁻¹ *
        (suzukiSourceLogFourierPolarizedForm (u + v) (u + v) -
          suzukiSourceLogFourierPolarizedForm (u - v) (u - v) -
          Complex.I *
            suzukiSourceLogFourierPolarizedForm
              (u + Complex.I • v) (u + Complex.I • v) +
          Complex.I *
            suzukiSourceLogFourierPolarizedForm
              (u - Complex.I • v) (u - Complex.I • v)) := by
  have hp := integrable_suzukiSourceLogFourierPolarizedIntegrand (u + v) (u + v)
  have hq := integrable_suzukiSourceLogFourierPolarizedIntegrand (u - v) (u - v)
  have hr := integrable_suzukiSourceLogFourierPolarizedIntegrand
    (u + Complex.I • v) (u + Complex.I • v)
  have hs := integrable_suzukiSourceLogFourierPolarizedIntegrand
    (u - Complex.I • v) (u - Complex.I • v)
  unfold suzukiSourceLogFourierPolarizedForm
  change (∫ xi : Real, suzukiSourceLogFourierPolarizedIntegrand v u xi) = _
  rw [show (∫ xi : Real, suzukiSourceLogFourierPolarizedIntegrand v u xi) =
      ∫ xi : Real,
        (4 : Complex)⁻¹ *
          (suzukiSourceLogFourierPolarizedIntegrand (u + v) (u + v) xi -
            suzukiSourceLogFourierPolarizedIntegrand (u - v) (u - v) xi -
            Complex.I * suzukiSourceLogFourierPolarizedIntegrand
              (u + Complex.I • v) (u + Complex.I • v) xi +
            Complex.I * suzukiSourceLogFourierPolarizedIntegrand
              (u - Complex.I • v) (u - Complex.I • v) xi) by
    apply integral_congr_ae
    filter_upwards with xi
    exact suzukiSourceLogFourierPolarizedIntegrand_reverse_eq_polarization u v xi]
  rw [integral_const_mul]
  rw [integral_add]
  · rw [integral_sub]
    · rw [integral_sub]
      · rw [integral_const_mul, integral_const_mul]
        rfl
      · exact hp
      · exact hq
    · exact hp.sub hq
    · exact hr.const_mul Complex.I
  · exact (hp.sub hq).sub (hr.const_mul Complex.I)
  · exact hs.const_mul Complex.I

/-- Complex polarization of Suzuki's checked logarithmic smooth-core
quadratic form. -/
def suzukiSourceLogFourierCorePolarizedForm
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) : Complex :=
  (4 : Complex)⁻¹ *
    ((suzukiSourceLogFourierForm (u + v).1 : Real) -
      (suzukiSourceLogFourierForm (u - v).1 : Real) -
      Complex.I *
        (suzukiSourceLogFourierForm (u + Complex.I • v).1 : Real) +
      Complex.I *
        (suzukiSourceLogFourierForm (u - Complex.I • v).1 : Real))

/-- The custom smooth-core polarization is the literal Suzuki weighted
Fourier integral, with reversed arguments to match the comparison form's
conjugate-linearity convention. -/
theorem suzukiSourceLogFourierCorePolarizedForm_eq_source
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceLogFourierCorePolarizedForm u v =
      suzukiSourceLogFourierPolarizedForm v.1 u.1 := by
  rw [suzukiSourceLogFourierPolarizedForm_reverse_eq_polarization]
  unfold suzukiSourceLogFourierCorePolarizedForm
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
  rw [suzukiSourceLogFourierPolarizedForm_self,
    suzukiSourceLogFourierPolarizedForm_self,
    suzukiSourceLogFourierPolarizedForm_self,
    suzukiSourceLogFourierPolarizedForm_self]

theorem suzukiYoshidaComparisonForm_core_self
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiYoshidaComparisonForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) =
      (suzukiSourceLogFourierForm v.1 : Real) := by
  apply Complex.ext
  · exact suzukiYoshidaComparisonForm_core_self_re v
  · have hsym :=
      suzukiYoshidaComparisonForm_conj_symm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v)
    have him := congrArg Complex.im hsym
    rw [Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

theorem suzukiYoshidaComparisonForm_core_polarized
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiYoshidaComparisonForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) =
      suzukiSourceLogFourierCorePolarizedForm u v := by
  have hplus := suzukiYoshidaComparisonForm_core_self (u + v)
  have hminus := suzukiYoshidaComparisonForm_core_self (u - v)
  have hiPlus :=
    suzukiYoshidaComparisonForm_core_self (u + Complex.I • v)
  have hiMinus :=
    suzukiYoshidaComparisonForm_core_self (u - Complex.I • v)
  simp only [map_add] at hplus
  simp only [map_sub] at hminus
  simp only [map_add, map_smul] at hiPlus
  simp only [map_sub, map_smul] at hiMinus
  rw [suzukiYoshidaComparisonForm_eq_polarization]
  unfold suzukiSourceLogFourierCorePolarizedForm
  rw [hplus, hminus, hiPlus, hiMinus]

set_option maxHeartbeats 800000 in
theorem suzukiYoshidaComparisonForm_tendsto
    {ι : Type*} {l : Filter ι}
    {u v : SuzukiYoshidaCorrectedCommonFormDomain}
    {a b : ι → SuzukiYoshidaCorrectedCommonFormDomain}
    (ha : Tendsto a l (𝓝 u)) (hb : Tendsto b l (𝓝 v)) :
    Tendsto (fun k => suzukiYoshidaComparisonForm (a k) (b k))
      l (𝓝 (suzukiYoshidaComparisonForm u v)) := by
  have hpair : Tendsto (fun k => (a k, b k)) l (𝓝 (u, v)) :=
    ha.prodMk_nhds hb
  have huncurried :
      Tendsto
        (fun k => Function.uncurry suzukiYoshidaComparisonForm (a k, b k))
        l
        (𝓝 (Function.uncurry suzukiYoshidaComparisonForm (u, v))) :=
    Filter.Tendsto.comp
      suzukiYoshidaComparisonForm_jointContinuous.continuousAt hpair
  simpa only [Function.uncurry_apply_pair] using huncurried

/-- Source-side comparison kernel obtained by taking the checked smooth-core
logarithmic Fourier polarizations along canonical dense-core approximations. -/
noncomputable def suzukiYoshidaComparisonLimitKernel
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Int) : Complex :=
  Filter.limUnder atTop fun k =>
    suzukiSourceLogFourierCorePolarizedForm
      (suzukiYoshidaCorrectedSmoothCoreApproximation
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m) k)
      (suzukiYoshidaCorrectedSmoothCoreApproximation
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) k)

/-- The comparison limit kernel is a limit of Suzuki's literal weighted
Fourier integrals.  The order `n, m` records the source form's
linear-in-the-first convention against the comparison form's
conjugate-linear-in-the-first convention. -/
theorem suzukiYoshidaComparisonLimitKernel_eq_sourceFourierLimit
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Int) :
    suzukiYoshidaComparisonLimitKernel hsource m n =
      Filter.limUnder atTop fun k =>
        suzukiSourceLogFourierPolarizedForm
          (suzukiYoshidaCorrectedSmoothCoreApproximation
            (suzukiYoshidaExponentialLinearCompletionOfSource
              hsource suzukiProjectAStar_pos n) k).1
          (suzukiYoshidaCorrectedSmoothCoreApproximation
            (suzukiYoshidaExponentialLinearCompletionOfSource
              hsource suzukiProjectAStar_pos m) k).1 := by
  unfold suzukiYoshidaComparisonLimitKernel
  congr 1
  funext k
  exact suzukiSourceLogFourierCorePolarizedForm_eq_source _ _

theorem suzukiYoshidaComparisonForm_exponential_eq_limitKernel
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Int) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaComparisonLimitKernel hsource m n := by
  let u := suzukiYoshidaExponentialLinearCompletionOfSource
    hsource suzukiProjectAStar_pos m
  let v := suzukiYoshidaExponentialLinearCompletionOfSource
    hsource suzukiProjectAStar_pos n
  have hform := suzukiYoshidaComparisonForm_tendsto
    (suzukiYoshidaCorrectedSmoothCoreApproximation_tendsto u)
    (suzukiYoshidaCorrectedSmoothCoreApproximation_tendsto v)
  have hsourceForm :
      Tendsto
        (fun k =>
          suzukiSourceLogFourierCorePolarizedForm
            (suzukiYoshidaCorrectedSmoothCoreApproximation u k)
            (suzukiYoshidaCorrectedSmoothCoreApproximation v k))
        atTop (𝓝 (suzukiYoshidaComparisonForm u v)) := by
    apply hform.congr'
    filter_upwards with k
    exact suzukiYoshidaComparisonForm_core_polarized _ _
  exact hsourceForm.limUnder_eq.symm

/-! ## Source-integral normalization -/

/-- Source-side comparison transform.  Positive modes are the literal
singular sine integral; mode zero retains the separate constant-mode endpoint
normalization. -/
def suzukiYoshidaComparisonSourceSineTransform (mode : Nat) : Real :=
  if mode = 0 then
    suzukiDF6D4ComparisonSineTransform 0
  else
    -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      (1 / (2 * t)) *
        Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))

/-- The source-side singular integral has exactly the DF6D4 comparison
normalization at every mode. -/
theorem suzukiYoshidaComparisonSourceSineTransform_eq_df6d4
    (mode : Nat) :
    suzukiYoshidaComparisonSourceSineTransform mode =
      suzukiDF6D4ComparisonSineTransform mode := by
  by_cases hmode : mode = 0
  · simp [suzukiYoshidaComparisonSourceSineTransform, hmode]
  · rw [suzukiYoshidaComparisonSourceSineTransform, if_neg hmode]
    exact (suzukiDF6D4ComparisonSineTransform_normalization'
      mode (Nat.one_le_iff_ne_zero.mpr hmode)).symm

/-- Ordered even convolution written with the source-side singular sine
integral rather than the independently frozen DF6D4 transform. -/
def suzukiYoshidaComparisonEvenSourceIntegral
    (left right : Nat) : Real :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  ((1 / 2 : Real) * suzukiDF6D4EvenModeScale left *
      suzukiDF6D4EvenModeScale right * Real.pi⁻¹) *
    (((differenceCoefficient : Rat) : Real) *
        (suzukiYoshidaComparisonSourceSineTransform right -
          suzukiYoshidaComparisonSourceSineTransform left) +
      ((totalCoefficient : Rat) : Real) *
        (suzukiYoshidaComparisonSourceSineTransform left +
          suzukiYoshidaComparisonSourceSineTransform right))

/-- Ordered odd convolution written with the source-side singular sine
integral. -/
def suzukiYoshidaComparisonOddSourceIntegral
    (left right : Nat) : Real :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  ((1 / 2 : Real) * Real.pi⁻¹) *
    (((differenceCoefficient : Rat) : Real) *
        (suzukiYoshidaComparisonSourceSineTransform right -
          suzukiYoshidaComparisonSourceSineTransform left) +
      ((totalCoefficient : Rat) : Real) *
        (suzukiYoshidaComparisonSourceSineTransform left +
          suzukiYoshidaComparisonSourceSineTransform right))

theorem suzukiYoshidaComparisonEvenSourceIntegral_eq_df6d4
    (left right : Nat) :
    suzukiYoshidaComparisonEvenSourceIntegral left right =
      suzukiDF6D4ComparisonEvenOffDiagonal left right := by
  unfold suzukiYoshidaComparisonEvenSourceIntegral
    suzukiDF6D4ComparisonEvenOffDiagonal
  rw [suzukiYoshidaComparisonSourceSineTransform_eq_df6d4,
    suzukiYoshidaComparisonSourceSineTransform_eq_df6d4]

theorem suzukiYoshidaComparisonOddSourceIntegral_eq_df6d4
    (left right : Nat) :
    suzukiYoshidaComparisonOddSourceIntegral left right =
      suzukiDF6D4ComparisonOddOffDiagonal left right := by
  unfold suzukiYoshidaComparisonOddSourceIntegral
    suzukiDF6D4ComparisonOddOffDiagonal
  rw [suzukiYoshidaComparisonSourceSineTransform_eq_df6d4,
    suzukiYoshidaComparisonSourceSineTransform_eq_df6d4]

/-! ## Limit-kernel parity assembly -/

theorem suzukiYoshidaComparisonForm_evenSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Nat) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) m n := by
  unfold suzukiYoshidaEvenLinearCompletionOfSource
    suzukiYoshidaEvenSourceKernelPairing
  split_ifs with hm hn hn
  · simpa using
      suzukiYoshidaComparisonForm_exponential_eq_limitKernel
        hsource 0 0
  · rw [suzukiYoshidaComparisonForm_smul_right,
      suzukiYoshidaComparisonForm_add_right]
    simp_rw [suzukiYoshidaComparisonForm_exponential_eq_limitKernel]
  · rw [suzukiYoshidaComparisonForm_smul_left,
      suzukiYoshidaComparisonForm_add_left]
    simp_rw [suzukiYoshidaComparisonForm_exponential_eq_limitKernel]
  · rw [suzukiYoshidaComparisonForm_smul_left,
      suzukiYoshidaComparisonForm_smul_right,
      suzukiYoshidaComparisonForm_add_left,
      suzukiYoshidaComparisonForm_add_right,
      suzukiYoshidaComparisonForm_add_right]
    simp_rw [suzukiYoshidaComparisonForm_exponential_eq_limitKernel]
    ring

theorem suzukiYoshidaComparisonForm_oddSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Nat) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaOddSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) m n := by
  unfold suzukiYoshidaOddLinearCompletionOfSource
    suzukiYoshidaOddSourceKernelPairing
  rw [suzukiYoshidaComparisonForm_smul_left,
    suzukiYoshidaComparisonForm_smul_right,
    suzukiYoshidaComparisonForm_sub_left,
    suzukiYoshidaComparisonForm_sub_right,
    suzukiYoshidaComparisonForm_sub_right]
  simp_rw [suzukiYoshidaComparisonForm_exponential_eq_limitKernel]
  ring

/-- The remaining analytic comparison statement after continuity,
polarization, parity assembly, and DF6D4 normalization have been removed.  It
compares only the source-side smooth-core limit kernel with the explicit
singular-integral convolutions. -/
def SuzukiYoshidaComparisonLimitKernelSourceIntegralNormalization
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  (∀ left right : Nat, left < right →
      suzukiYoshidaEvenSourceKernelPairing
          (suzukiYoshidaComparisonLimitKernel hsource) left right =
        (suzukiYoshidaComparisonEvenSourceIntegral left right : Complex)) ∧
    (∀ left right : Nat, 0 < left → left < right →
      suzukiYoshidaOddSourceKernelPairing
          (suzukiYoshidaComparisonLimitKernel hsource) left right =
        (suzukiYoshidaComparisonOddSourceIntegral left right : Complex))

/-- Remaining source theorem for ordered even comparison entries, stated
against the explicit singular-integral convolution rather than DF6D4. -/
def SuzukiEquation25EvenOffDiagonalComparisonSourceIntegralEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ left right : Nat, left < right →
    suzukiYoshidaComparisonForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      (suzukiYoshidaComparisonEvenSourceIntegral left right : Complex)

/-- Remaining source theorem for ordered positive odd comparison entries. -/
def SuzukiEquation25OddOffDiagonalComparisonSourceIntegralEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ left right : Nat, 0 < left → left < right →
    suzukiYoshidaComparisonForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      (suzukiYoshidaComparisonOddSourceIntegral left right : Complex)

theorem suzukiEquation25ComparisonSourceIntegralEvaluations_of_limitKernel
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hnormalization :
      SuzukiYoshidaComparisonLimitKernelSourceIntegralNormalization
        hsource) :
    SuzukiEquation25EvenOffDiagonalComparisonSourceIntegralEvaluation
        hsource ∧
      SuzukiEquation25OddOffDiagonalComparisonSourceIntegralEvaluation
        hsource := by
  constructor
  · intro left right hlt
    rw [suzukiYoshidaComparisonForm_evenSource]
    exact hnormalization.1 left right hlt
  · intro left right hleft hlt
    rw [suzukiYoshidaComparisonForm_oddSource]
    exact hnormalization.2 left right hleft hlt

/-- The explicit even source integral evaluation discharges the original
B3Q-G comparison component. -/
theorem suzukiEquation25EvenOffDiagonalComparisonEvaluation_of_sourceIntegral
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hevaluation :
      SuzukiEquation25EvenOffDiagonalComparisonSourceIntegralEvaluation
        hsource) :
    SuzukiEquation25EvenOffDiagonalComparisonEvaluation hsource := by
  intro left right hlt
  rw [hevaluation left right hlt,
    suzukiYoshidaComparisonEvenSourceIntegral_eq_df6d4]

/-- The explicit odd source integral evaluation discharges the original
B3Q-G comparison component. -/
theorem suzukiEquation25OddOffDiagonalComparisonEvaluation_of_sourceIntegral
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hevaluation :
      SuzukiEquation25OddOffDiagonalComparisonSourceIntegralEvaluation
        hsource) :
    SuzukiEquation25OddOffDiagonalComparisonEvaluation hsource := by
  intro left right hleft hlt
  rw [hevaluation left right hleft hlt,
    suzukiYoshidaComparisonOddSourceIntegral_eq_df6d4]

/-- End-to-end comparison-component assembly from the sole remaining
source-limit kernel normalization. -/
theorem suzukiEquation25OffDiagonalComparisonEvaluations_of_limitKernel
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hnormalization :
      SuzukiYoshidaComparisonLimitKernelSourceIntegralNormalization
        hsource) :
    SuzukiEquation25EvenOffDiagonalComparisonEvaluation hsource ∧
      SuzukiEquation25OddOffDiagonalComparisonEvaluation hsource := by
  obtain ⟨heven, hodd⟩ :=
    suzukiEquation25ComparisonSourceIntegralEvaluations_of_limitKernel
      hsource hnormalization
  exact
    ⟨suzukiEquation25EvenOffDiagonalComparisonEvaluation_of_sourceIntegral
        hsource heven,
      suzukiEquation25OddOffDiagonalComparisonEvaluation_of_sourceIntegral
        hsource hodd⟩

end

end RiemannHypothesisProject.Experiments.M100
