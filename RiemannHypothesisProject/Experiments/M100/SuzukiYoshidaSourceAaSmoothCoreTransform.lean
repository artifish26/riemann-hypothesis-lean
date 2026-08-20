import RiemannHypothesisProject.Experiments.M100.SuzukiScalarKernelBridge
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaSmoothCoreWeilFormula

/-!
# M100-DF6F smooth-core transform normalization

This module removes the interval-`L²` coordinate from Suzuki's literal zero
pairing on the smooth core.  The compact-interval Fourier evaluation is
exactly Suzuki's global Fourier--Laplace integral of the original supported
Schwartz function.  Thus the remaining Guinand--Weil source theorem can be
stated directly in the literature-facing transform normalization.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open SchwartzLineTestFunction

open scoped ComplexConjugate Convolution InnerProductSpace

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiSourceSmoothCoreTransformFiniteMeasure (a : Real) :
    IsFiniteMeasure (volume : Measure (SuzukiFiniteInterval a)) :=
  ⟨by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
    exact measure_Icc_lt_top⟩

/-- Restricting a supported smooth-core function to finite-interval `L²` does
not change its Fourier--Laplace integral. -/
theorem suzukiFiniteIntervalFourierValue_smoothCore_eq_suzukiFourierSource
    {a : Real} (v : SuzukiSmoothCoreLinearSubmodule a) (z : Complex) :
    suzukiFiniteIntervalFourierValue a
        (suzukiSmoothCoreFiniteIntervalL2LinearMap a v) z =
      suzukiFourierSource v.1 z := by
  let f : Real → Complex := fun x =>
    Complex.exp (Complex.I * z * (x : Complex)) * v.1 x
  have hcoe :
      (suzukiSmoothCoreFiniteIntervalL2LinearMap a v :
          SuzukiFiniteInterval a → Complex) =ᵐ[volume]
        fun x => v.1 x.1 := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (suzukiSmoothCoreFiniteIntervalContinuous
        (suzukiSmoothCoreLinearSubmoduleAsCore v))
  have hindicator : (Icc (-a) a).indicator f = f := by
    funext x
    by_cases hx : x ∈ Icc (-a) a
    · simp [hx]
    · have hvx : v.1 x = 0 := by
        by_contra hne
        exact hx ⟨(v.2 hne).1.le, (v.2 hne).2.le⟩
      simp [f, hx, hvx]
  rw [suzukiFiniteIntervalFourierValue_eq_integral]
  calc
    (∫ x : SuzukiFiniteInterval a,
        Complex.exp (Complex.I * z * (x.1 : Complex)) *
          (suzukiSmoothCoreFiniteIntervalL2LinearMap a v) x) =
        ∫ x : SuzukiFiniteInterval a,
          Complex.exp (Complex.I * z * (x.1 : Complex)) * v.1 x.1 := by
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
    _ = ∫ x in Icc (-a) a, f x := by
      simpa only [f] using (integral_subtype measurableSet_Icc f)
    _ = ∫ x : Real, f x := by
      rw [← integral_indicator measurableSet_Icc, hindicator]
    _ = suzukiFourierSource v.1 z := by
      simp only [f, suzukiFourierSource]
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      ring

/-- On the smooth core, the transform entering Suzuki's literal zero pairing
is the global supported Fourier--Laplace source at Suzuki's zero coordinate. -/
theorem suzukiSourceWeilTransform_smoothCore_eq_suzukiFourierSource
    {a : Real} (v : SuzukiSmoothCoreLinearSubmodule a) (rho : Complex) :
    suzukiSourceWeilTransform a
        (suzukiSmoothCoreFiniteIntervalL2LinearMap a v) rho =
      suzukiFourierSource v.1 (suzukiSourceGammaArgument rho) := by
  exact suzukiFiniteIntervalFourierValue_smoothCore_eq_suzukiFourierSource
    v (suzukiSourceGammaArgument rho)

/-- Multiplying a compactly supported Schwartz function by a complex
Fourier--Laplace exponential preserves integrability. -/
private theorem integrable_suzukiFourierSourceIntegrand_of_support_subset_Icc
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Icc (-a) a) (z : Complex) :
    Integrable (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * v x) := by
  have hsub : Function.support
      (fun x : Real =>
        Complex.exp ((x : Complex) * Complex.I * z) * v x) ⊆
        Icc (-a) a := by
    intro x hx
    exact hsupport (fun hv => hx (by simp [hv]))
  apply (integrableOn_iff_integrable_of_support_subset hsub).mp
  exact (by fun_prop : Continuous (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * v x)).continuousOn
    |>.integrableOn_compact isCompact_Icc

/-- The Fourier--Laplace integral of the reflected conjugate is the conjugate
integral at the conjugate frequency. -/
private theorem integral_suzukiFourierSourceIntegrand_star_eq_conj
    (v : SchwartzLineTestFunction) (z : Complex) :
    (∫ x : Real,
        Complex.exp ((x : Complex) * Complex.I * z) * star v x) =
      conj (suzukiFourierSource v (conj z)) := by
  have hreflect := integral_neg_eq_self
    (f := fun x : Real =>
      Complex.exp ((-x : Real) * Complex.I * z) * conj (v x)) volume
  calc
    (∫ x : Real,
        Complex.exp ((x : Complex) * Complex.I * z) * star v x) =
        ∫ x : Real,
          Complex.exp ((-x : Real) * Complex.I * z) * conj (v x) := by
      simpa only [star_apply, neg_neg, Complex.ofReal_neg] using hreflect
    _ = conj (suzukiFourierSource v (conj z)) := by
      rw [suzukiFourierSource, ← integral_conj]
      apply integral_congr_ae
      filter_upwards with x
      rw [map_mul, ← Complex.exp_conj]
      congr 2
      simp

/-- The supported Fourier--Laplace transform of an autocorrelation factors
at every complex frequency, not only on the real Fourier axis. -/
theorem suzukiFourierSource_autocorrelation_eq_mul_conj
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Icc (-a) a) (z : Complex) :
    suzukiFourierSource (SchwartzLineTestFunction.autocorrelation v) z =
      suzukiFourierSource v z * conj (suzukiFourierSource v (conj z)) := by
  let f : Real → Complex := fun x =>
    Complex.exp ((x : Complex) * Complex.I * z) * v x
  let g : Real → Complex := fun x =>
    Complex.exp ((x : Complex) * Complex.I * z) * star v x
  have hsupportStar :
      Function.support (SchwartzLineTestFunction.star v) ⊆ Icc (-a) a := by
    intro x hx
    have hv : v (-x) ≠ 0 := by
      intro hzero
      exact hx (by simp [star_apply, hzero])
    have hmem := hsupport hv
    constructor <;> linarith [hmem.1, hmem.2]
  have hf : Integrable f :=
    integrable_suzukiFourierSourceIntegrand_of_support_subset_Icc hsupport z
  have hg : Integrable g :=
    integrable_suzukiFourierSourceIntegrand_of_support_subset_Icc
      hsupportStar z
  have hpointwise (x : Real) :
      Complex.exp ((x : Complex) * Complex.I * z) *
          SchwartzLineTestFunction.autocorrelation v x =
        (f ⋆[ContinuousLinearMap.mul Complex Complex] g) x := by
    rw [SchwartzLineTestFunction.autocorrelation_apply,
      MeasureTheory.convolution_def, MeasureTheory.convolution_def,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have hexp :
        Complex.exp ((x : Complex) * Complex.I * z) =
          Complex.exp ((y : Complex) * Complex.I * z) *
            Complex.exp (((x - y : Real) : Complex) * Complex.I * z) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [f, g]
    rw [hexp]
    simp only [ContinuousLinearMap.mul_apply']
    ring
  rw [suzukiFourierSource]
  calc
    (∫ x : Real,
        Complex.exp ((x : Complex) * Complex.I * z) *
          SchwartzLineTestFunction.autocorrelation v x) =
        ∫ x : Real,
          (f ⋆[ContinuousLinearMap.mul Complex Complex] g) x := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpointwise x
    _ = (∫ x : Real, f x) * ∫ x : Real, g x := by
      simpa using MeasureTheory.integral_convolution
        (ContinuousLinearMap.mul Complex Complex) hf hg
    _ = suzukiFourierSource v z *
        conj (suzukiFourierSource v (conj z)) := by
      rw [integral_suzukiFourierSourceIntegrand_star_eq_conj]
      rfl

/-- Suzuki's source zero coordinate intertwines functional reflection with
complex conjugation. -/
theorem conj_suzukiSourceGammaArgument (rho : Complex) :
    conj (suzukiSourceGammaArgument rho) =
      suzukiSourceGammaArgument (1 - conj rho) := by
  rw [suzukiSourceGammaArgument_eq, suzukiSourceGammaArgument_eq]
  apply Complex.ext <;> simp <;> ring

/-- On a supported smooth-core function, one diagonal Weil product is exactly
the autocorrelation transform at Suzuki's source zero coordinate. -/
theorem suzukiFourierSource_autocorrelation_at_gamma
    {a : Real} (v : SuzukiSmoothCoreLinearSubmodule a) (rho : Complex) :
    suzukiFourierSource
        (SchwartzLineTestFunction.autocorrelation v.1)
        (suzukiSourceGammaArgument rho) =
      suzukiFourierSource v.1 (suzukiSourceGammaArgument rho) *
        conj (suzukiFourierSource v.1
          (suzukiSourceGammaArgument (1 - conj rho))) := by
  rw [suzukiFourierSource_autocorrelation_eq_mul_conj
    (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩),
    conj_suzukiSourceGammaArgument]

/-- Each diagonal Weil-pairing summand is the multiplicity-weighted sum of
the two source-autocorrelation evaluations in its conjugate zero pair. -/
theorem zetaWeilPairingSummand_smoothCore_self_eq_autocorrelation
    {a : Real} (v : SuzukiSmoothCoreLinearSubmodule a)
    (rho : ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype) :
    ComplexCompactExhaustion.zetaWeilPairingSummand
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
        rho =
      (ComplexCompactExhaustion.zetaZeroMultiplicity rho.1 : Complex) *
        (suzukiFourierSource
            (SchwartzLineTestFunction.autocorrelation v.1)
            (suzukiSourceGammaArgument (rho : Complex)) +
          suzukiFourierSource
            (SchwartzLineTestFunction.autocorrelation v.1)
            (suzukiSourceGammaArgument (conj (rho : Complex)))) := by
  have hfirst :=
    suzukiFourierSource_autocorrelation_at_gamma v (rho : Complex)
  have hsecond :=
    suzukiFourierSource_autocorrelation_at_gamma v (conj (rho : Complex))
  simp only [Complex.conj_conj] at hsecond
  rw [ComplexCompactExhaustion.zetaWeilPairingSummand, ← hfirst, ← hsecond]

/-- Suzuki's smooth-core Weil form written directly with the supported global
Fourier--Laplace source.  The arguments follow the project form convention:
the underlying Suzuki pairing receives the second argument first. -/
def suzukiSourceSmoothCoreFourierWeilPairing
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) : Complex :=
  ComplexCompactExhaustion.zetaWeilPairing
    (fun rho => suzukiFourierSource v.1 (suzukiSourceGammaArgument rho))
    (fun rho => suzukiFourierSource u.1 (suzukiSourceGammaArgument rho))

/-- The literal interval-`L²` pairing and the direct smooth-core Fourier
pairing are definitionally different presentations of the same zero sum. -/
theorem suzukiSourceLocalizedWeilPairing_smoothCore_eq_fourier
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceLocalizedWeilPairing suzukiProjectAStar
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar v)
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u) =
      suzukiSourceSmoothCoreFourierWeilPairing u v := by
  unfold suzukiSourceLocalizedWeilPairing
  unfold suzukiSourceSmoothCoreFourierWeilPairing
  congr 1
  · funext rho
    exact suzukiSourceWeilTransform_smoothCore_eq_suzukiFourierSource v rho
  · funext rho
    exact suzukiSourceWeilTransform_smoothCore_eq_suzukiFourierSource u rho

/-- The remaining Guinand--Weil theorem after removing all interval-`L²`
bookkeeping: the direct supported Fourier zero pairing is the polarized Burnol
residual. -/
def SuzukiSourceAaSmoothCoreFourierGuinandWeilFormula : Prop :=
  ∀ u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
    suzukiSourceSmoothCoreFourierWeilPairing u v =
      suzukiSourceSmoothCoreResidualPolarization u v

/-- The direct Fourier source statement is exactly equivalent to the earlier
literal interval-`L²` formulation. -/
theorem suzukiSourceAaSmoothCoreGuinandWeilFormula_iff_fourier :
    SuzukiSourceAaSmoothCoreGuinandWeilFormula ↔
      SuzukiSourceAaSmoothCoreFourierGuinandWeilFormula := by
  constructor
  · intro hformula u v
    rw [← suzukiSourceLocalizedWeilPairing_smoothCore_eq_fourier u v]
    exact hformula u v
  · intro hformula u v
    rw [suzukiSourceLocalizedWeilPairing_smoothCore_eq_fourier u v]
    exact hformula u v

/-- Endpoint receiver exposing only the direct supported Fourier source
formula, with the interval normalization discharged locally. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_fourierGuinandWeil
    (A : SuzukiSourceAaOperator)
    (hsourceGraph : SuzukiSourceAaLocalizedWeilAssociatedRepresentation A)
    (hbounded : SuzukiSourceAaLocalizedWeilFormBounded)
    (hformula : SuzukiSourceAaSmoothCoreFourierGuinandWeilFormula) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator :=
  sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_smoothCoreGuinandWeil
    A hsourceGraph hbounded
      (suzukiSourceAaSmoothCoreGuinandWeilFormula_iff_fourier.mpr hformula)

end

end RiemannHypothesisProject.Experiments.M100
