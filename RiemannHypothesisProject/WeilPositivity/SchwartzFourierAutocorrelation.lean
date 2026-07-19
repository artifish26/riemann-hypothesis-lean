import RiemannHypothesisProject.WeilPositivity.SchwartzAutocorrelation
import RiemannHypothesisProject.WeilPositivity.SchwartzPointwiseProduct

/-!
# Fourier normalization of Schwartz autocorrelation

The Guinand-Weil formula consumes a spectral test.  An additive-log base test
therefore enters the formula through the Fourier transform of its convolution
square.  This module proves the normalization instead of identifying the raw
convolution with the spectral test by definition.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open scoped ComplexConjugate FourierTransform

namespace SchwartzLineTestFunction

noncomputable section

/-- Fourier transform turns reflection-conjugation into pointwise complex
conjugation, with no sign change in the frequency. -/
theorem fourier_star_apply (f : SchwartzLineTestFunction) (t : Real) :
    (𝓕 (star f)) t = conj ((𝓕 f) t) := by
  change
    (𝓕 fun x : Real => conj (f (-x))) t =
      conj ((𝓕 fun x : Real => f x) t)
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  simp only [smul_eq_mul]
  rw [← integral_neg_eq_self
    (fun x : Real =>
      Complex.exp ((-2 * Real.pi * x * t : Real) * Complex.I) *
        conj (f (-x))) volume]
  apply integral_congr_ae
  filter_upwards with x
  simp only [neg_neg, map_mul]
  rw [← Complex.exp_conj]
  have harg :
      (((-2 * Real.pi * (-x) * t : Real) : Complex) * Complex.I) =
        conj (((-2 * Real.pi * x * t : Real) : Complex) * Complex.I) := by
    apply Complex.ext <;> simp
  rw [harg]

/-- The formula-facing spectral test attached to an additive-log base test. -/
noncomputable def fourierAutocorrelation
    (g : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  𝓕 (autocorrelation g)

/-- Fourier autocorrelation is the pointwise squared norm of the base
transform.  This freezes Mathlib's `exp (-2*pi*i*x*xi)` convention. -/
theorem fourierAutocorrelation_apply
    (g : SchwartzLineTestFunction) (t : Real) :
    fourierAutocorrelation g t =
      (𝓕 g) t * conj ((𝓕 g) t) := by
  rw [fourierAutocorrelation, autocorrelation]
  change
    (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul Complex Complex)
      g (star g))) t = _
  rw [SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply, fourier_star_apply]
  rfl

/-- In real coordinates the normalized autocorrelation is nonnegative. -/
theorem fourierAutocorrelation_re_nonneg
    (g : SchwartzLineTestFunction) (t : Real) :
    0 <= (fourierAutocorrelation g t).re := by
  rw [fourierAutocorrelation_apply, Complex.mul_conj]
  simp [Complex.normSq_nonneg]

/-- The Fourier-normalized autocorrelation is real-valued. -/
theorem fourierAutocorrelation_im
    (g : SchwartzLineTestFunction) (t : Real) :
    (fourierAutocorrelation g t).im = 0 := by
  rw [fourierAutocorrelation_apply, Complex.mul_conj]
  simp

/-- Fourier autocorrelation is the jointly continuous pointwise product of
the Fourier transform and its pointwise conjugate. -/
theorem fourierAutocorrelation_eq_pointwiseProduct
    (g : SchwartzLineTestFunction) :
    fourierAutocorrelation g =
      pointwiseProduct (𝓕 g) (conjugate (𝓕 g)) := by
  ext t
  rw [fourierAutocorrelation_apply]
  simp

/-- The formula-facing Fourier autocorrelation varies continuously in the
Schwartz topology. -/
theorem continuous_fourierAutocorrelation :
    Continuous fourierAutocorrelation := by
  have hpair : Continuous
      (fun g : SchwartzLineTestFunction =>
        ((𝓕 g : SchwartzLineTestFunction), conjugate (𝓕 g))) :=
    (SchwartzMap.fourierTransformCLM Complex).continuous.prodMk
      (conjugate.continuous.comp
        (SchwartzMap.fourierTransformCLM Complex).continuous)
  have hproduct := continuous_pointwiseProduct.comp hpair
  apply hproduct.congr
  intro g
  exact (fourierAutocorrelation_eq_pointwiseProduct g).symm

/-- Ordinary autocorrelation is continuous as a Schwartz-valued quadratic
map.  This follows from the checked Fourier normalization and Fourier
inversion, not from separate continuity of convolution. -/
theorem continuous_autocorrelation :
    Continuous autocorrelation := by
  have hinverse : Continuous
      (fun g : SchwartzLineTestFunction =>
        (𝓕⁻ (fourierAutocorrelation g) : SchwartzLineTestFunction)) :=
    (FourierTransform.fourierInvCLM Complex SchwartzLineTestFunction).continuous.comp
      continuous_fourierAutocorrelation
  apply hinverse.congr
  intro g
  simp [fourierAutocorrelation]

end

end SchwartzLineTestFunction

namespace SchwartzWeilQuadraticFormData

/-- A continuous explicit-formula functional yields a genuinely continuous
Weil quadratic form after autocorrelation. -/
theorem continuous_quadraticForm
    (data : SchwartzWeilQuadraticFormData)
    (hcontinuous : Continuous data.formulaFunctional) :
    Continuous data.quadraticForm :=
  hcontinuous.comp SchwartzLineTestFunction.continuous_autocorrelation

end SchwartzWeilQuadraticFormData

end RiemannHypothesisProject
