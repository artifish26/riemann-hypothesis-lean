import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianSchwartzSource

/-!
# Fourier transforms of polynomial-Gaussian sources

This module begins the Fourier-side analytic identification for the concrete
Hermite source family.  It proves an explicit transform formula for every
monomial times the `pi`-normalized Gaussian by differentiating the Gaussian's
self-Fourier identity.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- Every real monomial times the `pi`-Gaussian is integrable. -/
theorem integrable_pow_smul_guinandWeilPiGaussianSource_real
    (n : Nat) :
    Integrable fun x : Real =>
      x ^ n • guinandWeilPiGaussianSource (x : Complex) := by
  have h :=
    (guinandWeilPiPolynomialGaussianSchwartz
      ((Polynomial.X : Polynomial Complex) ^ n)).integrable (μ := volume)
  apply h.congr
  filter_upwards with x
  simp [guinandWeilPiPolynomialGaussianSource]

/--
The Fourier transform of `x^n exp (-pi x^2)` is the corresponding Hermite
derivative of the Gaussian, with the exact project Fourier normalization.
-/
theorem fourier_pow_mul_guinandWeilPiGaussianSource_real
    (n : Nat) :
    (𝓕 fun x : Real =>
      (x : Complex) ^ n * guinandWeilPiGaussianSource (x : Complex)) =
      fun t : Real =>
        ((-(2 : Complex) * (Real.pi : Complex) * Complex.I) ^ n)⁻¹ *
          guinandWeilPiPolynomialGaussianSource
            (guinandWeilPiPolynomialGaussianDerivativePolynomial n 1)
            (t : Complex) := by
  let g : Real -> Complex := fun x =>
    guinandWeilPiGaussianSource (x : Complex)
  let monomialGaussian : Real -> Complex := fun x =>
    (x : Complex) ^ n * g x
  let c : Complex :=
    (-(2 : Complex) * (Real.pi : Complex) * Complex.I) ^ n
  have hall :
      ∀ j : Nat, (j : ℕ∞) <= (n : ℕ∞) ->
        Integrable (fun x : Real => x ^ j • g x) := by
    intro j _hj
    simpa [g] using integrable_pow_smul_guinandWeilPiGaussianSource_real j
  have hiter :
      iteratedDeriv n (𝓕 g) =
        𝓕 (fun x : Real =>
          (-(2 : Complex) * (Real.pi : Complex) * Complex.I * x) ^ n •
            g x) :=
    Real.iteratedDeriv_fourier (N := n) hall le_rfl
  have hgaussian : 𝓕 g = g := by
    simpa [g] using fourier_guinandWeilPiGaussianSource_real
  rw [hgaussian] at hiter
  have hinside :
      (fun x : Real =>
          (-(2 : Complex) * (Real.pi : Complex) * Complex.I * x) ^ n •
            g x) =
        c • monomialGaussian := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    dsimp [c, monomialGaussian]
    rw [mul_pow]
    ring
  have hfourier_smul :
      𝓕 (c • monomialGaussian) = c • 𝓕 monomialGaussian := by
    funext t
    simp only [Pi.smul_apply, Real.fourier_real_eq]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with x
    simp [Circle.smul_def, mul_assoc, mul_comm]
  rw [hinside, hfourier_smul] at hiter
  have hc : c ≠ 0 := by
    dsimp [c]
    exact pow_ne_zero n
      (mul_ne_zero
        (mul_ne_zero (neg_ne_zero.mpr (OfNat.ofNat_ne_zero 2))
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero)
  funext t
  have ht :
      iteratedDeriv n g t = c * (𝓕 monomialGaussian) t := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hiter t
  have hderiv :
      iteratedDeriv n g t =
        guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiPolynomialGaussianDerivativePolynomial n 1)
          (t : Complex) := by
    simpa [g, guinandWeilPiPolynomialGaussianSource] using
      iteratedDeriv_guinandWeilPiPolynomialGaussianSource_real n 1 t
  change (𝓕 monomialGaussian) t =
    c⁻¹ *
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiPolynomialGaussianDerivativePolynomial n 1)
        (t : Complex)
  calc
    (𝓕 monomialGaussian) t = c⁻¹ * (c * (𝓕 monomialGaussian) t) := by
      field_simp
    _ = c⁻¹ * iteratedDeriv n g t := by rw [ht]
    _ = c⁻¹ *
        guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiPolynomialGaussianDerivativePolynomial n 1)
          (t : Complex) := by rw [hderiv]

/-- The explicit polynomial induced by Fourier transform on Gaussian sources. -/
def guinandWeilPiPolynomialGaussianFourierPolynomial
    (p : Polynomial Complex) : Polynomial Complex :=
  ∑ i ∈ p.support,
    Polynomial.C
        (p.coeff i *
          ((-(2 : Complex) * (Real.pi : Complex) * Complex.I) ^ i)⁻¹) *
      guinandWeilPiPolynomialGaussianDerivativePolynomial i 1

/-- A polynomial-Gaussian Schwartz test is the sum of its monomial tests. -/
theorem guinandWeilPiPolynomialGaussianSchwartz_eq_sum_monomials
    (p : Polynomial Complex) :
    guinandWeilPiPolynomialGaussianSchwartz p =
      ∑ i ∈ p.support,
        p.coeff i •
          guinandWeilPiPolynomialGaussianSchwartz
            ((Polynomial.X : Polynomial Complex) ^ i) := by
  ext x
  rw [guinandWeilPiPolynomialGaussianSchwartz_apply]
  conv_lhs =>
    rw [p.as_sum_support_C_mul_X_pow]
  simp [guinandWeilPiPolynomialGaussianSource, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Fourier transform of a monomial-Gaussian project Schwartz test. -/
theorem fourier_guinandWeilPiPolynomialGaussianSchwartz_monomial_apply
    (n : Nat) (t : Real) :
    (SchwartzLineTestFunction.fourier
      (guinandWeilPiPolynomialGaussianSchwartz
        ((Polynomial.X : Polynomial Complex) ^ n))) t =
      ((-(2 : Complex) * (Real.pi : Complex) * Complex.I) ^ n)⁻¹ *
        guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiPolynomialGaussianDerivativePolynomial n 1)
          (t : Complex) := by
  change
    (𝓕 fun x : Real =>
      guinandWeilPiPolynomialGaussianSchwartz
        ((Polynomial.X : Polynomial Complex) ^ n) x) t = _
  simpa [guinandWeilPiPolynomialGaussianSource] using
    congrFun (fourier_pow_mul_guinandWeilPiGaussianSource_real n) t

/--
The whole polynomial-Gaussian Schwartz family is stable under Fourier
transform, with the transformed polynomial given explicitly above.
-/
theorem fourier_guinandWeilPiPolynomialGaussianSchwartz
    (p : Polynomial Complex) :
    SchwartzLineTestFunction.fourier
        (guinandWeilPiPolynomialGaussianSchwartz p) =
      guinandWeilPiPolynomialGaussianSchwartz
        (guinandWeilPiPolynomialGaussianFourierPolynomial p) := by
  rw [guinandWeilPiPolynomialGaussianSchwartz_eq_sum_monomials]
  change
    SchwartzMap.fourierTransformCLM Complex
        (∑ i ∈ p.support,
          p.coeff i •
            guinandWeilPiPolynomialGaussianSchwartz
              ((Polynomial.X : Polynomial Complex) ^ i)) = _
  rw [map_sum]
  simp_rw [map_smul]
  ext t
  rw [SchwartzMap.sum_apply]
  simp_rw [SchwartzMap.smul_apply]
  change
    (∑ i ∈ p.support,
      p.coeff i *
        (SchwartzMap.fourierTransformCLM Complex
          (guinandWeilPiPolynomialGaussianSchwartz
            ((Polynomial.X : Polynomial Complex) ^ i))) t) =
      guinandWeilPiPolynomialGaussianSchwartz
        (guinandWeilPiPolynomialGaussianFourierPolynomial p) t
  have hmonomial (i : Nat) :
      (SchwartzMap.fourierTransformCLM Complex
        (guinandWeilPiPolynomialGaussianSchwartz
          ((Polynomial.X : Polynomial Complex) ^ i))) t =
        ((-(2 : Complex) * (Real.pi : Complex) * Complex.I) ^ i)⁻¹ *
          guinandWeilPiPolynomialGaussianSource
            (guinandWeilPiPolynomialGaussianDerivativePolynomial i 1)
            (t : Complex) :=
    fourier_guinandWeilPiPolynomialGaussianSchwartz_monomial_apply i t
  simp_rw [hmonomial]
  rw [guinandWeilPiPolynomialGaussianSchwartz_apply]
  simp [guinandWeilPiPolynomialGaussianFourierPolynomial,
    guinandWeilPiPolynomialGaussianSource, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

end

end RiemannHypothesisProject
