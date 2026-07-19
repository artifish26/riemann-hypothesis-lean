import RiemannHypothesisProject.GuinandWeilConcrete.EvenPolynomialGaussianSource

/-!
# Polynomial-Gaussian weights for the xi rectangle

This module defines the real-even entire weight used in the selected direct
Guinand-Weil contour proof.  The fixed rectangle has vertical sides
`re s = -1/4` and `re s = 5/4`; after the spectral change of variables its
horizontal edges lie in the polynomial-Gaussian strip `abs (im z) <= 3/4`.

The results here are source and source-coordinate bridge theorems.  They do
not assume a contour identity or an explicit formula.
-/

namespace RiemannHypothesisProject

open scoped ComplexConjugate

noncomputable section

/-- The fixed right vertical line in the selected xi contour. -/
def guinandWeilXiContourRight : Real := 5 / 4

/-- The fixed left vertical line, obtained from the right line by `s -> 1-s`. -/
def guinandWeilXiContourLeft : Real := -1 / 4

/-- The entire real-even polynomial-Gaussian weight in xi coordinates. -/
def guinandWeilXiContourWeight
    (p : Polynomial Real) (s : Complex) : Complex :=
  guinandWeilPiPolynomialGaussianSource
    (guinandWeilPiEvenPolynomial p)
    ((s - (1 / 2 : Complex)) / Complex.I)

/-- The spectral coordinate of a point `sigma + i*T` on the xi rectangle. -/
theorem guinandWeilXiContourCoordinate_horizontal
    (sigma T : Real) :
    ((((sigma : Complex) + (T : Complex) * Complex.I) -
          (1 / 2 : Complex)) / Complex.I) =
      (T : Complex) + ((1 / 2 - sigma : Real) : Complex) * Complex.I := by
  apply Complex.ext <;> simp

/-- The contour weight is entire. -/
theorem differentiable_guinandWeilXiContourWeight (p : Polynomial Real) :
    Differentiable Complex (guinandWeilXiContourWeight p) := by
  have hsource :
      Differentiable Complex
        (guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p)) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp
      (analyticOnNhd_guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p))
  have hcoordinate :
      Differentiable Complex
        (fun s : Complex => (s - (1 / 2 : Complex)) / Complex.I) := by
    fun_prop
  exact hsource.comp hcoordinate

/-- Analytic form of the entire contour-weight theorem. -/
theorem analyticOnNhd_guinandWeilXiContourWeight (p : Polynomial Real) :
    AnalyticOnNhd Complex (guinandWeilXiContourWeight p) Set.univ := by
  exact Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (differentiable_guinandWeilXiContourWeight p)

/-- Reflection of the xi variable negates the spectral coordinate. -/
theorem guinandWeilXiContourCoordinate_one_sub (s : Complex) :
    (((1 - s) - (1 / 2 : Complex)) / Complex.I) =
      -((s - (1 / 2 : Complex)) / Complex.I) := by
  field_simp [Complex.I_ne_zero]
  ring

/-- The real-even contour weight respects xi's reflection symmetry. -/
theorem guinandWeilXiContourWeight_one_sub
    (p : Polynomial Real) (s : Complex) :
    guinandWeilXiContourWeight p (1 - s) =
      guinandWeilXiContourWeight p s := by
  unfold guinandWeilXiContourWeight
  rw [guinandWeilXiContourCoordinate_one_sub,
    guinandWeilPiEvenPolynomialGaussianSource_neg]

/-- Conjugating the xi variable gives the negative conjugate spectral
coordinate. -/
theorem guinandWeilXiContourCoordinate_conj (s : Complex) :
    ((conj s - (1 / 2 : Complex)) / Complex.I) =
      -conj ((s - (1 / 2 : Complex)) / Complex.I) := by
  apply Complex.ext <;> simp

/-- The contour weight commutes with complex conjugation. -/
theorem guinandWeilXiContourWeight_conj
    (p : Polynomial Real) (s : Complex) :
    guinandWeilXiContourWeight p (conj s) =
      conj (guinandWeilXiContourWeight p s) := by
  unfold guinandWeilXiContourWeight
  rw [guinandWeilXiContourCoordinate_conj,
    guinandWeilPiEvenPolynomialGaussianSource_neg,
    guinandWeilPiEvenPolynomialGaussianSource_conj]

/-- The fixed xi strip maps into the source strip of half-width `3/4`. -/
theorem abs_half_sub_le_three_quarters_of_mem_xiContourStrip
    {sigma : Real}
    (hleft : guinandWeilXiContourLeft <= sigma)
    (hright : sigma <= guinandWeilXiContourRight) :
    abs (1 / 2 - sigma) <= (3 / 4 : Real) := by
  rw [abs_le]
  constructor <;>
    norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight] at hleft hright ⊢ <;>
    linarith

/-- Uniform Gaussian edge bound on the complete fixed xi strip.  The
polynomial exponent is the actual degree of the selected even source, while
the constant is independent of both the horizontal coordinate and the edge
height. -/
theorem exists_pos_const_norm_guinandWeilXiContourWeight_horizontal_le
    (p : Polynomial Real) :
    ∃ C : Real, 0 < C ∧
      ∀ sigma T : Real,
        guinandWeilXiContourLeft ≤ sigma →
        sigma ≤ guinandWeilXiContourRight →
        norm (guinandWeilXiContourWeight p
          ((sigma : Complex) + (T : Complex) * Complex.I)) ≤
          C * (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
            Real.exp (-Real.pi * T ^ 2) := by
  let q : Polynomial Complex := guinandWeilPiEvenPolynomial p
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow q with
    ⟨B, hB_pos, hB⟩
  let E : Real := Real.exp (Real.pi * (3 / 4 : Real) ^ 2)
  refine ⟨B * E, mul_pos hB_pos (Real.exp_pos _), ?_⟩
  intro sigma T hleft hright
  let y : Real := 1 / 2 - sigma
  let z : Complex := (T : Complex) + (y : Complex) * Complex.I
  have hy : abs y ≤ (3 / 4 : Real) := by
    exact abs_half_sub_le_three_quarters_of_mem_xiContourStrip hleft hright
  have hcoordinate :
      guinandWeilXiContourWeight p
          ((sigma : Complex) + (T : Complex) * Complex.I) =
        guinandWeilPiPolynomialGaussianSource q z := by
    simp only [guinandWeilXiContourWeight, q, z, y]
    rw [guinandWeilXiContourCoordinate_horizontal]
  rw [hcoordinate, guinandWeilPiPolynomialGaussianSource, norm_mul]
  have hpolynomial :
      norm (q.aeval z) ≤ B * (norm z + 2) ^ q.natDegree := hB z
  have hz_norm : norm z ≤ abs T + abs y := by
    calc
      norm z ≤ norm (T : Complex) + norm ((y : Complex) * Complex.I) := by
        exact norm_add_le _ _
      _ = abs T + abs y := by simp [Real.norm_eq_abs]
  have hradius : norm z + 2 ≤ abs T + 3 := by
    linarith
  have hbase_nonneg : 0 ≤ norm z + 2 := by positivity
  have hpower :
      (norm z + 2) ^ q.natDegree ≤ (abs T + 3) ^ q.natDegree :=
    pow_le_pow_left₀ hbase_nonneg hradius q.natDegree
  have hy_sq : y ^ 2 ≤ (3 / 4 : Real) ^ 2 :=
    sq_le_sq.mpr (by
      simpa [abs_of_nonneg (by norm_num : (0 : Real) ≤ 3 / 4)] using hy)
  have hgaussian :
      norm (guinandWeilPiGaussianSource z) ≤
        E * Real.exp (-Real.pi * T ^ 2) := by
    rw [show norm (guinandWeilPiGaussianSource z) =
        Real.exp (Real.pi * (y ^ 2 - T ^ 2)) by
      simpa [z] using norm_guinandWeilPiGaussianSource_horizontalLine T y]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  calc
    norm (q.aeval z) * norm (guinandWeilPiGaussianSource z) ≤
        (B * (norm z + 2) ^ q.natDegree) *
          (E * Real.exp (-Real.pi * T ^ 2)) := by
      exact mul_le_mul hpolynomial hgaussian (norm_nonneg _) (by positivity)
    _ ≤ (B * (abs T + 3) ^ q.natDegree) *
          (E * Real.exp (-Real.pi * T ^ 2)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower hB_pos.le) (by positivity)
    _ = (B * E) * (abs T + 3) ^ q.natDegree *
          Real.exp (-Real.pi * T ^ 2) := by ring

end

end RiemannHypothesisProject
