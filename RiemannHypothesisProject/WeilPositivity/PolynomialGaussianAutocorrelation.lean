import RiemannHypothesisProject.GuinandWeilConcrete.EvenPolynomialGaussianSource
import RiemannHypothesisProject.WeilPositivity.SchwartzFourierAutocorrelation

/-!
# Polynomial-Gaussian autocorrelation source

The proved Guinand-Weil contour theorem uses `p(z) * exp (-pi*z^2)`.  A Weil
square reaches that exact scale when the base transform uses the half-Gaussian
`q(z^2 / 2) * exp (-pi*z^2 / 2)`.  We construct the additive-log base test by
inverse Fourier transform and check the scale change algebraically.
-/

namespace RiemannHypothesisProject

open scoped ComplexConjugate FourierTransform

noncomputable section

/-- Scaling by `1 / sqrt 2` on the real line. -/
noncomputable def zetaWeilHalfScaleEquiv : Real ≃L[Real] Real :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 ((Real.sqrt 2)⁻¹)
      (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))))

@[simp]
theorem zetaWeilHalfScaleEquiv_apply (x : Real) :
    zetaWeilHalfScaleEquiv x = (Real.sqrt 2)⁻¹ * x :=
  rfl

/-- The half-Gaussian entire transform attached to a real even polynomial. -/
def zetaWeilHalfGaussianEntire
    (q : Polynomial Real) (z : Complex) : Complex :=
  guinandWeilPiPolynomialGaussianSource (guinandWeilPiEvenPolynomial q)
    (((Real.sqrt 2)⁻¹ : Real) * z)

/-- Its real restriction as an actual Schwartz function. -/
noncomputable def zetaWeilHalfGaussianSpectrum
    (q : Polynomial Real) : SchwartzLineTestFunction :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Real zetaWeilHalfScaleEquiv
    (guinandWeilPiEvenPolynomialGaussianSchwartz q)

@[simp]
theorem zetaWeilHalfGaussianSpectrum_apply
    (q : Polynomial Real) (x : Real) :
    zetaWeilHalfGaussianSpectrum q x =
      zetaWeilHalfGaussianEntire q (x : Complex) :=
  by
    simp [zetaWeilHalfGaussianSpectrum, zetaWeilHalfGaussianEntire,
      zetaWeilHalfScaleEquiv]

/-- The additive-log base test whose Fourier transform is the selected
half-Gaussian spectrum. -/
noncomputable def zetaWeilPolynomialGaussianBase
    (q : Polynomial Real) : SchwartzLineTestFunction :=
  (FourierTransform.fourierCLE Complex SchwartzLineTestFunction).symm
    (zetaWeilHalfGaussianSpectrum q)

/-- The base test has exactly the selected half-Gaussian Fourier transform. -/
theorem fourier_zetaWeilPolynomialGaussianBase
    (q : Polynomial Real) :
    𝓕 (zetaWeilPolynomialGaussianBase q) =
      zetaWeilHalfGaussianSpectrum q :=
  (FourierTransform.fourierCLE Complex SchwartzLineTestFunction).apply_symm_apply
    (zetaWeilHalfGaussianSpectrum q)

/-- The real polynomial multiplying the full `pi`-Gaussian after taking the
Weil square. -/
noncomputable def zetaWeilAutocorrelationPolynomial
    (q : Polynomial Real) : Polynomial Real :=
  (q.comp (Polynomial.C (1 / 2 : Real) * Polynomial.X)) ^ 2

/-- The half-Gaussian entire transform is even. -/
theorem zetaWeilHalfGaussianEntire_neg
    (q : Polynomial Real) (z : Complex) :
    zetaWeilHalfGaussianEntire q (-z) =
      zetaWeilHalfGaussianEntire q z := by
  unfold zetaWeilHalfGaussianEntire
  convert guinandWeilPiEvenPolynomialGaussianSource_neg q
    ((((Real.sqrt 2)⁻¹ : Real) : Complex) * z) using 1
  all_goals ring_nf

/-- The half-Gaussian entire transform has the required real structure. -/
theorem zetaWeilHalfGaussianEntire_conj
    (q : Polynomial Real) (z : Complex) :
    zetaWeilHalfGaussianEntire q (conj z) =
      conj (zetaWeilHalfGaussianEntire q z) := by
  unfold zetaWeilHalfGaussianEntire
  convert guinandWeilPiEvenPolynomialGaussianSource_conj q
    ((((Real.sqrt 2)⁻¹ : Real) : Complex) * z) using 1
  all_goals simp

/-- Squaring the half-Gaussian gives exactly the polynomial-Gaussian source
accepted by the unconditional literature formula. -/
theorem zetaWeilHalfGaussianEntire_sq
    (q : Polynomial Real) (z : Complex) :
    zetaWeilHalfGaussianEntire q z ^ 2 =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial
          (zetaWeilAutocorrelationPolynomial q)) z := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : ((Real.sqrt 2)⁻¹ : Real) ^ 2 = 1 / 2 := by
    rw [inv_pow, hsqrt]
    norm_num
  have hcC : ((Real.sqrt 2 : Complex)⁻¹) ^ 2 = (1 / 2 : Complex) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, hc]
    norm_num
  rw [zetaWeilHalfGaussianEntire,
    guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiGaussianSource, guinandWeilPiGaussianSource]
  simp [guinandWeilPiEvenPolynomial, zetaWeilAutocorrelationPolynomial,
    Polynomial.aeval_def, Polynomial.eval_map]
  ring_nf
  rw [hcC]
  ring_nf
  have hExp :
      Complex.exp (z ^ 2 * (Real.pi : Complex) * (-1 / 2)) ^ 2 =
        Complex.exp (-(z ^ 2 * (Real.pi : Complex))) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  rw [hExp]

/-- The Fourier transform of the concrete convolution square is precisely the
full-scale polynomial-Gaussian formula test. -/
theorem fourierAutocorrelation_zetaWeilPolynomialGaussianBase
    (q : Polynomial Real) :
    SchwartzLineTestFunction.fourierAutocorrelation
        (zetaWeilPolynomialGaussianBase q) =
      guinandWeilPiEvenPolynomialGaussianSchwartz
        (zetaWeilAutocorrelationPolynomial q) := by
  ext t
  rw [SchwartzLineTestFunction.fourierAutocorrelation_apply]
  have hfourier := congrArg
    (fun f : SchwartzLineTestFunction => f t)
    (fourier_zetaWeilPolynomialGaussianBase q)
  rw [hfourier]
  have hreal :
      conj (zetaWeilHalfGaussianSpectrum q t) =
        zetaWeilHalfGaussianSpectrum q t := by
    apply Complex.conj_eq_iff_im.mpr
    change
      (guinandWeilPiEvenPolynomialGaussianSchwartz q
        ((Real.sqrt 2)⁻¹ * t)).im = 0
    exact guinandWeilPiEvenPolynomialGaussianSchwartz_im q _
  rw [hreal]
  rw [zetaWeilHalfGaussianSpectrum_apply,
    guinandWeilPiEvenPolynomialGaussianSchwartz_apply]
  simpa [pow_two] using zetaWeilHalfGaussianEntire_sq q (t : Complex)

end

end RiemannHypothesisProject
