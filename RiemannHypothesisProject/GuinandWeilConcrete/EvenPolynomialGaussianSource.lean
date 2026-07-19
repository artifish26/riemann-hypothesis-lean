import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianFourierSource

/-!
# Real and even polynomial-Gaussian sources

This module isolates the formula-compatible real/even part of the concrete
polynomial-Gaussian family and proves its source and Fourier symmetries.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open scoped ComplexConjugate FourierTransform

noncomputable section

/-- A real polynomial in `X^2`, extended to complex coefficients. -/
def guinandWeilPiEvenPolynomial
    (p : Polynomial Real) : Polynomial Complex :=
  (p.comp (Polynomial.X ^ 2)).map (algebraMap Real Complex)

/-- Evaluation of the even polynomial is unchanged by negating its argument. -/
theorem guinandWeilPiEvenPolynomial_aeval_neg
  (p : Polynomial Real) (z : Complex) :
    (guinandWeilPiEvenPolynomial p).aeval (-z) =
      (guinandWeilPiEvenPolynomial p).aeval z := by
  simp [guinandWeilPiEvenPolynomial, Polynomial.aeval_def,
    Polynomial.eval_map]

/-- The corresponding complex polynomial-Gaussian source is even. -/
theorem guinandWeilPiEvenPolynomialGaussianSource_neg
    (p : Polynomial Real) (z : Complex) :
    guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p) (-z) =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p) z := by
  rw [guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiEvenPolynomial_aeval_neg,
    guinandWeilPiGaussianSource_neg]

/-- The even polynomial-Gaussian source commutes with conjugation. -/
theorem guinandWeilPiEvenPolynomialGaussianSource_conj
    (p : Polynomial Real) (z : Complex) :
    guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p) (conj z) =
      conj
        (guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p) z) := by
  exact
    guinandWeilPiPolynomialGaussianSource_map_real_conj
      (p.comp (Polynomial.X ^ 2)) z

/-- The real restriction as an actual project Schwartz test. -/
noncomputable def guinandWeilPiEvenPolynomialGaussianSchwartz
    (p : Polynomial Real) : SchwartzLineTestFunction :=
  guinandWeilPiPolynomialGaussianSchwartz
    (guinandWeilPiEvenPolynomial p)

@[simp]
theorem guinandWeilPiEvenPolynomialGaussianSchwartz_apply
    (p : Polynomial Real) (x : Real) :
    guinandWeilPiEvenPolynomialGaussianSchwartz p x =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p) (x : Complex) :=
  rfl

/-- Every real restriction in the source family is even. -/
theorem guinandWeilPiEvenPolynomialGaussianSchwartz_neg
    (p : Polynomial Real) (x : Real) :
    guinandWeilPiEvenPolynomialGaussianSchwartz p (-x) =
      guinandWeilPiEvenPolynomialGaussianSchwartz p x := by
  simpa using guinandWeilPiEvenPolynomialGaussianSource_neg p (x : Complex)

/-- Every real restriction in the source family is real-valued. -/
theorem guinandWeilPiEvenPolynomialGaussianSchwartz_im
    (p : Polynomial Real) (x : Real) :
    (guinandWeilPiEvenPolynomialGaussianSchwartz p x).im = 0 := by
  exact
    guinandWeilPiPolynomialGaussianSource_map_real_ofReal_im
      (p.comp (Polynomial.X ^ 2)) x

/-- Fourier transform preserves evenness of an integrable even function. -/
theorem fourier_even_of_even
    (f : Real -> Complex)
    (hf_even : ∀ x : Real, f (-x) = f x)
    (t : Real) :
    (𝓕 f) (-t) = (𝓕 f) t := by
  have h :=
    Real.fourier_comp_linearIsometry
      (LinearIsometryEquiv.neg Real) f t
  have hcomp : f ∘ LinearIsometryEquiv.neg Real = f := by
    funext x
    exact hf_even x
  rw [hcomp] at h
  simpa using h.symm

/-- Fourier transform has conjugate symmetry for a real-valued input. -/
theorem conj_fourier_eq_fourier_neg_of_real
    (f : Real -> Complex)
    (hf_real : ∀ x : Real, conj (f x) = f x)
    (t : Real) :
    conj ((𝓕 f) t) = (𝓕 f) (-t) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, map_mul]
  rw [hf_real x, ← Complex.exp_conj]
  apply congrArg (fun w : Complex => w * f x)
  congr 1
  simp
  simp only [starRingEnd_apply, star_ofNat]
  ring_nf
  simp

/-- A real and even input has a real-valued Fourier transform. -/
theorem fourier_im_eq_zero_of_real_even
    (f : Real -> Complex)
    (hf_real : ∀ x : Real, conj (f x) = f x)
    (hf_even : ∀ x : Real, f (-x) = f x)
    (t : Real) :
    ((𝓕 f) t).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  calc
    conj ((𝓕 f) t) = (𝓕 f) (-t) :=
      conj_fourier_eq_fourier_neg_of_real f hf_real t
    _ = (𝓕 f) t := fourier_even_of_even f hf_even t

/-- The Fourier transform of every even polynomial-Gaussian is even. -/
theorem fourier_guinandWeilPiEvenPolynomialGaussianSchwartz_neg
    (p : Polynomial Real) (t : Real) :
    (SchwartzLineTestFunction.fourier
      (guinandWeilPiEvenPolynomialGaussianSchwartz p)) (-t) =
      (SchwartzLineTestFunction.fourier
        (guinandWeilPiEvenPolynomialGaussianSchwartz p)) t := by
  change
    (𝓕 fun x : Real =>
      guinandWeilPiEvenPolynomialGaussianSchwartz p x) (-t) =
    (𝓕 fun x : Real =>
      guinandWeilPiEvenPolynomialGaussianSchwartz p x) t
  exact fourier_even_of_even _
    (guinandWeilPiEvenPolynomialGaussianSchwartz_neg p) t

/-- The Fourier transform of every even real polynomial-Gaussian is real. -/
theorem fourier_guinandWeilPiEvenPolynomialGaussianSchwartz_im
    (p : Polynomial Real) (t : Real) :
    ((SchwartzLineTestFunction.fourier
      (guinandWeilPiEvenPolynomialGaussianSchwartz p)) t).im = 0 := by
  change
    ((𝓕 fun x : Real =>
      guinandWeilPiEvenPolynomialGaussianSchwartz p x) t).im = 0
  apply fourier_im_eq_zero_of_real_even
  · intro x
    exact Complex.conj_eq_iff_im.mpr
      (guinandWeilPiEvenPolynomialGaussianSchwartz_im p x)
  · exact guinandWeilPiEvenPolynomialGaussianSchwartz_neg p

end

end RiemannHypothesisProject
