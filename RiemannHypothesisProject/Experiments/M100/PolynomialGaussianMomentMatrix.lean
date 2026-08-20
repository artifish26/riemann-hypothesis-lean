import Mathlib.LinearAlgebra.Matrix.PosDef
import RiemannHypothesisProject.Experiments.M100.TwoBlockPSD
import RiemannHypothesisProject.GuinandWeilConcrete.EvenPolynomialGaussianSpan
import RiemannHypothesisProject.WeilPositivity.PolynomialGaussianAutocorrelation

/-!
# M100-X06 polynomial-Gaussian moment matrices

This experimental module polarizes the production polynomial-Gaussian base
tests and exposes their finite coefficient Gram matrices.  The specially
scaled monomial basis makes the matrix Hankel: its `(i,j)` entry depends only
on `i + j`.

Every theorem is finite-dimensional or algebraic.  No all-degree positivity,
criterion-determining promotion, or RH conclusion is asserted.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open scoped BigOperators ComplexConjugate FourierTransform Matrix
open SchwartzLineTestFunction

noncomputable section

/-- The polynomial multiplying the full Gaussian in the Fourier transform of
the ordered cross-correlation of the bases attached to `q` and `r`. -/
def zetaWeilCrossPolynomial
    (q r : Polynomial Real) : Polynomial Real :=
  q.comp (Polynomial.C (1 / 2 : Real) * Polynomial.X) *
    r.comp (Polynomial.C (1 / 2 : Real) * Polynomial.X)

/-- Doubling the polynomial variable is inverse to the half-scale used by the
production autocorrelation polynomial. -/
def zetaWeilDoubleScalePolynomial
    (q : Polynomial Real) : Polynomial Real :=
  q.comp (Polynomial.C (2 : Real) * Polynomial.X)

/-- Every ordinary polynomial square occurs as a production
polynomial-Gaussian autocorrelation polynomial after the explicit inverse
scaling. -/
theorem zetaWeilAutocorrelationPolynomial_doubleScale
    (q : Polynomial Real) :
    zetaWeilAutocorrelationPolynomial
        (zetaWeilDoubleScalePolynomial q) = q ^ 2 := by
  unfold zetaWeilAutocorrelationPolynomial zetaWeilDoubleScalePolynomial
  rw [Polynomial.comp_assoc]
  have hscale :
      (Polynomial.C (2 : Real) * Polynomial.X).comp
          (Polynomial.C (1 / 2 : Real) * Polynomial.X) =
        Polynomial.X := by
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
    rw [← mul_assoc, ← Polynomial.C_mul]
    norm_num
  rw [hscale, Polynomial.comp_X]

/-- Multiplying two half-Gaussian spectra gives the full-Gaussian source with
the cross polynomial. -/
theorem zetaWeilHalfGaussianEntire_mul
    (q r : Polynomial Real) (z : Complex) :
    zetaWeilHalfGaussianEntire q z * zetaWeilHalfGaussianEntire r z =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial (zetaWeilCrossPolynomial q r)) z := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : ((Real.sqrt 2)⁻¹ : Real) ^ 2 = 1 / 2 := by
    rw [inv_pow, hsqrt]
    norm_num
  have hcC : ((Real.sqrt 2 : Complex)⁻¹) ^ 2 = (1 / 2 : Complex) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, hc]
    norm_num
  rw [zetaWeilHalfGaussianEntire, zetaWeilHalfGaussianEntire,
    guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiGaussianSource]
  simp [guinandWeilPiEvenPolynomial, zetaWeilCrossPolynomial,
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
  rw [hExp, guinandWeilPiGaussianSource]
  ring_nf

/-- The ordered cross-correlation has an exact polynomial-Gaussian Fourier
transform. -/
theorem fourierCrossCorrelation_zetaWeilPolynomialGaussianBase
    (q r : Polynomial Real) :
    fourierSchwartzCrossCorrelation
        (zetaWeilPolynomialGaussianBase q)
        (zetaWeilPolynomialGaussianBase r) =
      guinandWeilPiEvenPolynomialGaussianSchwartz
        (zetaWeilCrossPolynomial q r) := by
  ext t
  rw [fourierSchwartzCrossCorrelation_apply]
  have hq := congrArg
    (fun f : SchwartzLineTestFunction => f t)
    (fourier_zetaWeilPolynomialGaussianBase q)
  have hr := congrArg
    (fun f : SchwartzLineTestFunction => f t)
    (fourier_zetaWeilPolynomialGaussianBase r)
  rw [hq, hr]
  have hreal :
      conj (zetaWeilHalfGaussianSpectrum r t) =
        zetaWeilHalfGaussianSpectrum r t := by
    apply Complex.conj_eq_iff_im.mpr
    change
      (guinandWeilPiEvenPolynomialGaussianSchwartz r
        ((Real.sqrt 2)⁻¹ * t)).im = 0
    exact guinandWeilPiEvenPolynomialGaussianSchwartz_im r _
  rw [hreal, zetaWeilHalfGaussianSpectrum_apply,
    zetaWeilHalfGaussianSpectrum_apply,
    guinandWeilPiEvenPolynomialGaussianSchwartz_apply]
  exact zetaWeilHalfGaussianEntire_mul q r (t : Complex)

/-- Reversing the two polynomial-Gaussian bases leaves their ordered
cross-correlation unchanged. -/
theorem schwartzCrossCorrelation_zetaWeilPolynomialGaussianBase_comm
    (q r : Polynomial Real) :
    schwartzCrossCorrelation
        (zetaWeilPolynomialGaussianBase q)
        (zetaWeilPolynomialGaussianBase r) =
      schwartzCrossCorrelation
        (zetaWeilPolynomialGaussianBase r)
        (zetaWeilPolynomialGaussianBase q) := by
  apply (FourierTransform.fourierCLE
    Complex SchwartzLineTestFunction).injective
  change fourierSchwartzCrossCorrelation
      (zetaWeilPolynomialGaussianBase q)
      (zetaWeilPolynomialGaussianBase r) =
    fourierSchwartzCrossCorrelation
      (zetaWeilPolynomialGaussianBase r)
      (zetaWeilPolynomialGaussianBase q)
  rw [fourierCrossCorrelation_zetaWeilPolynomialGaussianBase,
    fourierCrossCorrelation_zetaWeilPolynomialGaussianBase]
  congr 1
  simp only [zetaWeilCrossPolynomial]
  rw [mul_comm]

/-- A formula-facing polynomial moment test, obtained by inverse Fourier
transforming the full-scale even monomial-Gaussian. -/
def zetaWeilPolynomialGaussianMomentTest
    (n : Nat) : SchwartzLineTestFunction :=
  (FourierTransform.fourierCLE Complex SchwartzLineTestFunction).symm
    (guinandWeilPiEvenMonomialGaussianSchwartz n)

/-- The polynomial-Gaussian moment sequence seen by a checked Weil formula
functional. -/
def zetaWeilPolynomialGaussianMoment
    (data : SchwartzWeilQuadraticFormData) (n : Nat) : Real :=
  data.formulaFunctional (zetaWeilPolynomialGaussianMomentTest n)

/-- Scaling the `n`th monomial by `2^n` removes the half-Gaussian dilation
from its cross products. -/
def zetaWeilMomentBasisPolynomial (n : Nat) : Polynomial Real :=
  Polynomial.monomial n ((2 : Real) ^ n)

/-- The concrete base test for the scaled moment basis. -/
def zetaWeilMomentBasis (n : Nat) : SchwartzLineTestFunction :=
  zetaWeilPolynomialGaussianBase (zetaWeilMomentBasisPolynomial n)

/-- The scaled basis polynomial becomes the ordinary monomial after the
half-scale substitution. -/
theorem zetaWeilMomentBasisPolynomial_comp_halfScale (n : Nat) :
    (zetaWeilMomentBasisPolynomial n).comp
        (Polynomial.C (1 / 2 : Real) * Polynomial.X) =
      Polynomial.X ^ n := by
  rw [zetaWeilMomentBasisPolynomial, Polynomial.monomial_comp, mul_pow]
  rw [← mul_assoc, ← Polynomial.C_pow, ← Polynomial.C_mul]
  norm_num [← mul_pow]

/-- Cross products of scaled basis elements are ordinary monomials indexed by
the sum of the two degrees. -/
theorem zetaWeilCrossPolynomial_momentBasis
    (i j : Nat) :
    zetaWeilCrossPolynomial
        (zetaWeilMomentBasisPolynomial i)
        (zetaWeilMomentBasisPolynomial j) =
      Polynomial.basisMonomials Real (i + j) := by
  rw [zetaWeilCrossPolynomial,
    zetaWeilMomentBasisPolynomial_comp_halfScale,
    zetaWeilMomentBasisPolynomial_comp_halfScale,
    ← pow_add]
  rw [Polynomial.coe_basisMonomials]
  exact Polynomial.X_pow_eq_monomial (i + j)

/-- The cross-correlation of two scaled basis tests is exactly the inverse
Fourier moment test indexed by the sum of their degrees. -/
theorem schwartzCrossCorrelation_momentBasis
    (i j : Nat) :
    schwartzCrossCorrelation (zetaWeilMomentBasis i)
        (zetaWeilMomentBasis j) =
      zetaWeilPolynomialGaussianMomentTest (i + j) := by
  apply (FourierTransform.fourierCLE
    Complex SchwartzLineTestFunction).injective
  change fourierSchwartzCrossCorrelation
      (zetaWeilMomentBasis i) (zetaWeilMomentBasis j) =
    𝓕 (zetaWeilPolynomialGaussianMomentTest (i + j))
  rw [zetaWeilMomentBasis, zetaWeilMomentBasis,
    fourierCrossCorrelation_zetaWeilPolynomialGaussianBase,
    zetaWeilCrossPolynomial_momentBasis]
  simp [zetaWeilPolynomialGaussianMomentTest,
    guinandWeilPiEvenMonomialGaussianSchwartz,
    guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap]

/-- The polarized entry of two scaled basis tests is the corresponding
polynomial-Gaussian moment. -/
theorem schwartzWeilPolarizedForm_momentBasis
    (data : SchwartzWeilQuadraticFormData) (i j : Nat) :
    schwartzWeilPolarizedForm data
        (zetaWeilMomentBasis i) (zetaWeilMomentBasis j) =
      zetaWeilPolynomialGaussianMoment data (i + j) := by
  rw [schwartzWeilPolarizedForm]
  rw [schwartzCrossCorrelation_momentBasis,
    schwartzCrossCorrelation_momentBasis, Nat.add_comm j i, map_add]
  unfold zetaWeilPolynomialGaussianMoment
  ring

/-- The finite polynomial-Gaussian Gram matrix. -/
def zetaWeilPolynomialGaussianGram
    (data : SchwartzWeilQuadraticFormData) (N : Nat) :
    Matrix (Fin N) (Fin N) Real :=
  fun i j => schwartzWeilPolarizedForm data
    (zetaWeilMomentBasis i) (zetaWeilMomentBasis j)

/-- The finite Gram matrix is Hankel in the scaled monomial basis. -/
theorem zetaWeilPolynomialGaussianGram_apply
    (data : SchwartzWeilQuadraticFormData) (N : Nat)
    (i j : Fin N) :
    zetaWeilPolynomialGaussianGram data N i j =
      zetaWeilPolynomialGaussianMoment data ((i : Nat) + (j : Nat)) := by
  exact schwartzWeilPolarizedForm_momentBasis data i j

/-- The coefficient quadratic polynomial of the finite Hankel moment matrix. -/
def zetaWeilPolynomialGaussianMomentQuadratic
    (data : SchwartzWeilQuadraticFormData) (N : Nat)
    (c : Fin N → Real) : Real :=
  ∑ i : Fin N, ∑ j : Fin N,
    c i * c j *
      zetaWeilPolynomialGaussianMoment data ((i : Nat) + (j : Nat))

theorem schwartzWeilPolarizedForm_finset_sum_left
    {ι : Type*} (data : SchwartzWeilQuadraticFormData)
    (s : Finset ι) (f : ι → SchwartzLineTestFunction)
    (h : SchwartzLineTestFunction) :
    schwartzWeilPolarizedForm data (∑ i ∈ s, f i) h =
      ∑ i ∈ s, schwartzWeilPolarizedForm data (f i) h := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [schwartzWeilPolarizedForm, schwartzCrossCorrelation]
  | @insert a s ha ih =>
      simp [ha, schwartzWeilPolarizedForm_add_left, ih]

theorem schwartzWeilPolarizedForm_finset_sum_right
    {ι : Type*} (data : SchwartzWeilQuadraticFormData)
    (s : Finset ι) (f : ι → SchwartzLineTestFunction)
    (h : SchwartzLineTestFunction) :
    schwartzWeilPolarizedForm data h (∑ i ∈ s, f i) =
      ∑ i ∈ s, schwartzWeilPolarizedForm data h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [schwartzWeilPolarizedForm, schwartzCrossCorrelation]
  | @insert a s ha ih =>
      simp [ha, schwartzWeilPolarizedForm_add_right, ih]

/-- The quadratic form of a finite coefficient vector is exactly its Hankel
moment polynomial. -/
theorem quadraticForm_sum_momentBasis_eq_momentQuadratic
    (data : SchwartzWeilQuadraticFormData) (N : Nat)
    (c : Fin N → Real) :
    data.quadraticForm
        (∑ i : Fin N, c i • zetaWeilMomentBasis i) =
      zetaWeilPolynomialGaussianMomentQuadratic data N c := by
  rw [← schwartzWeilPolarizedForm_self]
  rw [schwartzWeilPolarizedForm_finset_sum_left]
  unfold zetaWeilPolynomialGaussianMomentQuadratic
  apply Finset.sum_congr rfl
  intro i hi
  rw [schwartzWeilPolarizedForm_real_smul_left]
  rw [schwartzWeilPolarizedForm_finset_sum_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwartzWeilPolarizedForm_real_smul_right,
    schwartzWeilPolarizedForm_momentBasis]
  ring

/-- Symmetry of polarization makes every finite polynomial-Gaussian Gram
matrix Hermitian. -/
theorem zetaWeilPolynomialGaussianGram_isHermitian
    (data : SchwartzWeilQuadraticFormData) (N : Nat) :
    (zetaWeilPolynomialGaussianGram data N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [zetaWeilPolynomialGaussianGram, star_trivial]
  exact schwartzWeilPolarizedForm_symm data _ _

/-- The matrix-vector quadratic expression is the same explicit moment
polynomial. -/
theorem zetaWeilPolynomialGaussianGram_dotProduct_mulVec
    (data : SchwartzWeilQuadraticFormData) (N : Nat)
    (c : Fin N → Real) :
    star c ⬝ᵥ (zetaWeilPolynomialGaussianGram data N *ᵥ c) =
      zetaWeilPolynomialGaussianMomentQuadratic data N c := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
  unfold zetaWeilPolynomialGaussianMomentQuadratic
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [zetaWeilPolynomialGaussianGram_apply]
  ring

/-- Exact finite-degree criterion: matrix PSD is equivalent to nonnegativity
of the checked Weil form on every coefficient combination in this finite
polynomial-Gaussian subspace. -/
theorem zetaWeilPolynomialGaussianGram_posSemidef_iff
    (data : SchwartzWeilQuadraticFormData) (N : Nat) :
    (zetaWeilPolynomialGaussianGram data N).PosSemidef ↔
      ∀ c : Fin N → Real,
        0 ≤ data.quadraticForm
          (∑ i : Fin N, c i • zetaWeilMomentBasis i) := by
  constructor
  · intro hPSD c
    have h := hPSD.dotProduct_mulVec_nonneg c
    rw [zetaWeilPolynomialGaussianGram_dotProduct_mulVec,
      ← quadraticForm_sum_momentBasis_eq_momentQuadratic] at h
    exact h
  · intro hnonnegative
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (zetaWeilPolynomialGaussianGram_isHermitian data N)
    intro c
    rw [zetaWeilPolynomialGaussianGram_dotProduct_mulVec,
      ← quadraticForm_sum_momentBasis_eq_momentQuadratic]
    exact hnonnegative c

end


end M100
end Experiments
end RiemannHypothesisProject
