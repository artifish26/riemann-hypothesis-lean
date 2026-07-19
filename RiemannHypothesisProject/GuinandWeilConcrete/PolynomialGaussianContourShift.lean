import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianFourierSource
import RiemannHypothesisProject.GuinandWeilConcrete.RectangleBoundaryIntegral

/-!
# Polynomial-Gaussian horizontal contour shifts

This module proves the exact contour shift used on the right vertical side of
the Guinand-Weil rectangle.  The proof is an actual infinite-rectangle
argument: finite Cauchy-Goursat identities are combined with uniform
polynomial-Gaussian decay on bounded horizontal strips.
-/

namespace RiemannHypothesisProject

open Complex Filter MeasureTheory Set Topology intervalIntegral
open scoped Interval Topology FourierTransform

noncomputable section

/-- The entire Fourier-kernel integrand before restricting to a horizontal line. -/
private def polynomialGaussianFourierKernel
    (p : Polynomial Complex) (u : Real) (z : Complex) : Complex :=
  guinandWeilPiPolynomialGaussianSource p z *
    Complex.exp (-Complex.I * (u : Complex) * z)

private theorem differentiable_polynomialGaussianFourierKernel
    (p : Polynomial Complex) (u : Real) :
    Differentiable Complex (polynomialGaussianFourierKernel p u) := by
  have hsource : Differentiable Complex
      (guinandWeilPiPolynomialGaussianSource p) :=
    p.differentiable_aeval.mul differentiable_guinandWeilPiGaussianSource
  have hkernel : Differentiable Complex
      (fun z : Complex => Complex.exp (-Complex.I * (u : Complex) * z)) := by
    fun_prop
  exact hsource.mul hkernel

/-- A polynomial-Gaussian Fourier integrand is integrable on every horizontal line. -/
theorem integrable_guinandWeilPiPolynomialGaussianSource_horizontalLine_mul_exp
    (p : Polynomial Complex) (u y : Real) :
    Integrable fun x : Real =>
      guinandWeilPiPolynomialGaussianSource p
          ((x : Complex) + (y : Complex) * Complex.I) *
        Complex.exp (-Complex.I * (u : Complex) * (x : Complex)) := by
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow p with
    ⟨B, hB_pos, hB⟩
  let C : Real :=
    B * (abs y + 2) ^ p.natDegree
  have hC_nonneg : 0 <= C := by
    exact mul_nonneg hB_pos.le (pow_nonneg (by positivity) _)
  have hbase : Integrable fun x : Real =>
      (abs x + 1) ^ p.natDegree *
        norm (guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) :=
    integrable_abs_add_one_pow_mul_norm_guinandWeilPiGaussianSource_horizontalLine
      p.natDegree y
  have hmajor : Integrable fun x : Real =>
      C * ((abs x + 1) ^ p.natDegree *
        norm (guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I))) :=
    hbase.const_mul C
  refine hmajor.mono' ?_ (Eventually.of_forall fun x => ?_)
  · have hsource : Continuous fun x : Real =>
        guinandWeilPiPolynomialGaussianSource p
          ((x : Complex) + (y : Complex) * Complex.I) :=
      (p.differentiable_aeval.mul
        differentiable_guinandWeilPiGaussianSource).continuous.comp (by fun_prop)
    have hkernel : Continuous fun x : Real =>
        Complex.exp (-Complex.I * (u : Complex) * (x : Complex)) := by
      fun_prop
    exact (hsource.mul hkernel).aestronglyMeasurable
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  have hz_radius : norm z + 2 <= (abs y + 2) * (abs x + 1) := by
    have hz_norm : norm z <= abs x + abs y := by
      calc
        norm z <= norm (x : Complex) + norm ((y : Complex) * Complex.I) :=
          norm_add_le _ _
        _ = abs x + abs y := by simp [Real.norm_eq_abs]
    have hxy :
        abs x + abs y + 2 <= (abs y + 2) * (abs x + 1) := by
      nlinarith [abs_nonneg x, abs_nonneg y]
    have hz_radius' : norm z + 2 <= abs x + abs y + 2 := by
      linarith
    exact hz_radius'.trans hxy
  have hz_radius_nonneg : 0 <= norm z + 2 := by positivity
  have hsource :
      norm (guinandWeilPiPolynomialGaussianSource p z) <=
        C * (abs x + 1) ^ p.natDegree *
          norm (guinandWeilPiGaussianSource z) := by
    rw [guinandWeilPiPolynomialGaussianSource, norm_mul]
    calc
      norm (p.aeval z) * norm (guinandWeilPiGaussianSource z) <=
          (B * (norm z + 2) ^ p.natDegree) *
            norm (guinandWeilPiGaussianSource z) :=
        mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)
      _ <= (B * ((abs y + 2) * (abs x + 1)) ^ p.natDegree) *
            norm (guinandWeilPiGaussianSource z) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hz_radius_nonneg hz_radius _) hB_pos.le)
          (norm_nonneg _)
      _ = C * (abs x + 1) ^ p.natDegree *
            norm (guinandWeilPiGaussianSource z) := by
        simp only [C, mul_pow]
        ring
  have hkernel_norm :
      norm (Complex.exp (-Complex.I * (u : Complex) * (x : Complex))) = 1 := by
    rw [show -Complex.I * (u : Complex) * (x : Complex) =
        Complex.I * (-(u * x) : Real) by
      apply Complex.ext <;> simp]
    exact Complex.norm_exp_I_mul_ofReal _
  rw [norm_mul, hkernel_norm, mul_one]
  simpa [C, z, Real.norm_eq_abs, abs_of_nonneg hC_nonneg, mul_assoc] using hsource

private theorem integrable_polynomialGaussianFourierKernel_horizontalLine
    (p : Polynomial Complex) (u y : Real) :
    Integrable fun x : Real =>
      polynomialGaussianFourierKernel p u
        ((x : Complex) + (y : Complex) * Complex.I) := by
  have h :=
    integrable_guinandWeilPiPolynomialGaussianSource_horizontalLine_mul_exp p u y
  have hfactor :
      (fun x : Real =>
        polynomialGaussianFourierKernel p u
          ((x : Complex) + (y : Complex) * Complex.I)) =
        fun x : Real =>
          Complex.exp ((u * y : Real) : Complex) *
            (guinandWeilPiPolynomialGaussianSource p
                ((x : Complex) + (y : Complex) * Complex.I) *
              Complex.exp (-Complex.I * (u : Complex) * (x : Complex))) := by
    funext x
    simp only [polynomialGaussianFourierKernel]
    rw [show -Complex.I * (u : Complex) *
          ((x : Complex) + (y : Complex) * Complex.I) =
        ((u * y : Real) : Complex) +
          (-Complex.I * (u : Complex) * (x : Complex)) by
      apply Complex.ext <;> simp]
    rw [Complex.exp_add]
    ring
  rw [hfactor]
  exact h.const_mul _

private theorem tendsto_polynomialGaussianFourierKernel_verticalIntegral_right
    (p : Polynomial Complex) (u y : Real) :
    Tendsto
      (fun T : Real => ∫ v in (0 : Real)..y,
        polynomialGaussianFourierKernel p u
          ((T : Complex) + (v : Complex) * Complex.I))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine Metric.tendsto_atTop.mpr ?_
  intro epsilon hepsilon
  let A : Real := abs y
  let K : Real := Real.exp (abs u * A)
  have hK_pos : 0 < K := Real.exp_pos _
  have hsmall :=
    eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_le_of_horizontalStrip
      p 0 (A := A) (epsilon := epsilon / (2 * max 1 (abs y) * K))
      (abs_nonneg y)
      (div_pos hepsilon
        (mul_pos (mul_pos (by norm_num) (lt_max_of_lt_left zero_lt_one)) hK_pos))
  have hsmall_atTop :
      Filter.Eventually (fun T : Real =>
        ∀ v : Real, abs v <= A ->
          norm (guinandWeilPiPolynomialGaussianSource p
              ((T : Complex) + (v : Complex) * Complex.I)) <=
            epsilon / (2 * max 1 (abs y) * K)) atTop := by
    filter_upwards [hsmall.filter_mono atTop_le_cocompact] with T hT v hv
    simpa using hT v hv
  rcases (eventually_atTop.1 hsmall_atTop) with ⟨N, hN⟩
  refine ⟨N, fun T hT => ?_⟩
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  apply lt_of_le_of_lt (intervalIntegral.norm_integral_le_of_norm_le_const ?_)
  · calc
      (epsilon / (2 * max 1 (abs y) * K) * K) * abs (y - 0) <=
          max 1 (abs y) * (epsilon / (2 * max 1 (abs y) * K) * K) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [sub_zero] using (le_max_right (1 : Real) (abs y)))
          (mul_nonneg (div_nonneg hepsilon.le (by positivity)) hK_pos.le)
      _ = epsilon / 2 := by
        field_simp [ne_of_gt hK_pos, ne_of_gt (lt_max_of_lt_left zero_lt_one)]
      _ < epsilon := by linarith
  · intro v hv
    have hv_abs : abs v <= A := by
      simpa [A] using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hv)
    have hsource := hN T hT v hv_abs
    simp only [polynomialGaussianFourierKernel, norm_mul, Complex.norm_exp]
    have hexp :
        Real.exp ((-Complex.I * (u : Complex) *
          ((T : Complex) + (v : Complex) * Complex.I)).re) <= K := by
      apply Real.exp_le_exp.mpr
      dsimp [K, A]
      have hre :
          (-Complex.I * (u : Complex) *
            ((T : Complex) + (v : Complex) * Complex.I)).re = u * v := by
        simp [mul_re]
      rw [hre]
      calc
        u * v <= abs (u * v) := le_abs_self _
        _ = abs u * abs v := abs_mul u v
        _ <= abs u * A := mul_le_mul_of_nonneg_left hv_abs (abs_nonneg u)
    exact mul_le_mul hsource hexp (Real.exp_pos _).le (by positivity)

private theorem tendsto_polynomialGaussianFourierKernel_verticalIntegral_left
    (p : Polynomial Complex) (u y : Real) :
    Tendsto
      (fun T : Real => ∫ v in (0 : Real)..y,
        polynomialGaussianFourierKernel p u
          ((-T : Real) + (v : Complex) * Complex.I))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine Metric.tendsto_atTop.mpr ?_
  intro epsilon hepsilon
  let A : Real := abs y
  let K : Real := Real.exp (abs u * A)
  have hK_pos : 0 < K := Real.exp_pos _
  have hsmall :=
    eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_le_of_horizontalStrip
      p 0 (A := A) (epsilon := epsilon / (2 * max 1 (abs y) * K))
      (abs_nonneg y)
      (div_pos hepsilon
        (mul_pos (mul_pos (by norm_num) (lt_max_of_lt_left zero_lt_one)) hK_pos))
  have hsmall_atTop :
      Filter.Eventually (fun T : Real =>
        ∀ v : Real, abs v <= A ->
          norm (guinandWeilPiPolynomialGaussianSource p
              ((-T : Real) + (v : Complex) * Complex.I)) <=
            epsilon / (2 * max 1 (abs y) * K)) atTop := by
    have hneg : Tendsto (fun T : Real => -T) atTop atBot := tendsto_neg_atTop_atBot
    have hcocompact : Tendsto (fun T : Real => -T) atTop (cocompact Real) :=
      hneg.mono_right atBot_le_cocompact
    filter_upwards [hcocompact.eventually hsmall] with T hT v hv
    simpa using hT v hv
  rcases (eventually_atTop.1 hsmall_atTop) with ⟨N, hN⟩
  refine ⟨N, fun T hT => ?_⟩
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  apply lt_of_le_of_lt (intervalIntegral.norm_integral_le_of_norm_le_const ?_)
  · calc
      (epsilon / (2 * max 1 (abs y) * K) * K) * abs (y - 0) <=
          max 1 (abs y) * (epsilon / (2 * max 1 (abs y) * K) * K) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [sub_zero] using (le_max_right (1 : Real) (abs y)))
          (mul_nonneg (div_nonneg hepsilon.le (by positivity)) hK_pos.le)
      _ = epsilon / 2 := by
        field_simp [ne_of_gt hK_pos, ne_of_gt (lt_max_of_lt_left zero_lt_one)]
      _ < epsilon := by linarith
  · intro v hv
    have hv_abs : abs v <= A := by
      simpa [A] using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hv)
    have hsource := hN T hT v hv_abs
    simp only [polynomialGaussianFourierKernel, norm_mul, Complex.norm_exp]
    have hexp :
        Real.exp ((-Complex.I * (u : Complex) *
          ((-T : Real) + (v : Complex) * Complex.I)).re) <= K := by
      apply Real.exp_le_exp.mpr
      dsimp [K, A]
      have hre :
          (-Complex.I * (u : Complex) *
            ((-T : Real) + (v : Complex) * Complex.I)).re = u * v := by
        simp [mul_re]
      rw [hre]
      calc
        u * v <= abs (u * v) := le_abs_self _
        _ = abs u * abs v := abs_mul u v
        _ <= abs u * A := mul_le_mul_of_nonneg_left hv_abs (abs_nonneg u)
    exact mul_le_mul hsource hexp (Real.exp_pos _).le (by positivity)

/--
The entire polynomial-Gaussian Fourier kernel has the same integral on every
horizontal line.  Both vertical edges are discharged by proved strip decay.
-/
theorem integral_polynomialGaussianFourierKernel_horizontalLine_eq_real
    (p : Polynomial Complex) (u y : Real) :
    (∫ x : Real,
        polynomialGaussianFourierKernel p u
          ((x : Complex) + (y : Complex) * Complex.I)) =
      ∫ x : Real, polynomialGaussianFourierKernel p u (x : Complex) := by
  let Iᵧ : Real → Complex := fun T => ∫ x in -T..T,
    polynomialGaussianFourierKernel p u
      ((x : Complex) + (y : Complex) * Complex.I)
  let I₀ : Real → Complex := fun T => ∫ x in -T..T,
    polynomialGaussianFourierKernel p u (x : Complex)
  let Vₙ : Real → Complex := fun T => ∫ v in (0 : Real)..y,
    polynomialGaussianFourierKernel p u
      ((T : Complex) + (v : Complex) * Complex.I)
  let Vₗ : Real → Complex := fun T => ∫ v in (0 : Real)..y,
    polynomialGaussianFourierKernel p u
      ((-T : Real) + (v : Complex) * Complex.I)
  have hrectangle (T : Real) :
      I₀ T - Iᵧ T + Complex.I * Vₙ T - Complex.I * Vₗ T = 0 := by
    have h := guinandWeilRectangleIntegral_eq_zero_of_differentiableOn
      (F := polynomialGaussianFourierKernel p u)
      (z := (-T : Complex))
      (w := (T : Complex) + (y : Complex) * Complex.I)
      (differentiable_polynomialGaussianFourierKernel p u).differentiableOn
    simpa [guinandWeilRectangleIntegral, guinandWeilHorizontalIntegral,
      guinandWeilVerticalIntegral, Iᵧ, I₀, Vₙ, Vₗ] using h
  have hfinite : Iᵧ = fun T => I₀ T + Complex.I * Vₙ T - Complex.I * Vₗ T := by
    funext T
    have h := hrectangle T
    linear_combination -h
  refine tendsto_nhds_unique
    (intervalIntegral_tendsto_integral
      (integrable_polynomialGaussianFourierKernel_horizontalLine p u y)
      tendsto_neg_atTop_atBot tendsto_id) ?_
  change Tendsto Iᵧ atTop _
  rw [hfinite]
  have hI₀ := intervalIntegral_tendsto_integral
    (integrable_polynomialGaussianFourierKernel_horizontalLine p u 0)
    tendsto_neg_atTop_atBot tendsto_id
  have hVₙ :=
    (tendsto_polynomialGaussianFourierKernel_verticalIntegral_right p u y).const_mul
      Complex.I
  have hVₗ :=
    (tendsto_polynomialGaussianFourierKernel_verticalIntegral_left p u y).const_mul
      Complex.I
  simpa [I₀, Vₙ, Vₗ] using (hI₀.add hVₙ).sub hVₗ

/--
Exact horizontal contour-shift factor for the unshifted real Fourier kernel.
The sign is fixed by `exp (-I*u*(x+I*y)) = exp (u*y) exp (-I*u*x)`.
-/
theorem integral_guinandWeilPiPolynomialGaussianSource_horizontalLine_mul_exp_eq
    (p : Polynomial Complex) (u y : Real) :
    (∫ x : Real,
        guinandWeilPiPolynomialGaussianSource p
            ((x : Complex) + (y : Complex) * Complex.I) *
          Complex.exp (-Complex.I * (u : Complex) * (x : Complex))) =
      Complex.exp ((-(u * y) : Real) : Complex) *
        ∫ x : Real,
          guinandWeilPiPolynomialGaussianSource p (x : Complex) *
            Complex.exp (-Complex.I * (u : Complex) * (x : Complex)) := by
  have hshift := integral_polynomialGaussianFourierKernel_horizontalLine_eq_real p u y
  have hline :
      (fun x : Real =>
        polynomialGaussianFourierKernel p u
          ((x : Complex) + (y : Complex) * Complex.I)) =
        fun x : Real =>
          Complex.exp ((u * y : Real) : Complex) *
            (guinandWeilPiPolynomialGaussianSource p
                ((x : Complex) + (y : Complex) * Complex.I) *
              Complex.exp (-Complex.I * (u : Complex) * (x : Complex))) := by
    funext x
    simp only [polynomialGaussianFourierKernel]
    rw [show -Complex.I * (u : Complex) *
          ((x : Complex) + (y : Complex) * Complex.I) =
        ((u * y : Real) : Complex) +
          (-Complex.I * (u : Complex) * (x : Complex)) by
      apply Complex.ext <;> simp]
    rw [Complex.exp_add]
    ring
  rw [hline, MeasureTheory.integral_const_mul] at hshift
  simp only [polynomialGaussianFourierKernel] at hshift
  calc
    (∫ x : Real,
        guinandWeilPiPolynomialGaussianSource p
            ((x : Complex) + (y : Complex) * Complex.I) *
          Complex.exp (-Complex.I * (u : Complex) * (x : Complex))) =
        Complex.exp ((-(u * y) : Real) : Complex) *
          (Complex.exp ((u * y : Real) : Complex) *
            ∫ x : Real,
              guinandWeilPiPolynomialGaussianSource p
                  ((x : Complex) + (y : Complex) * Complex.I) *
                Complex.exp (-Complex.I * (u : Complex) * (x : Complex))) := by
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    _ = Complex.exp ((-(u * y) : Real) : Complex) *
        ∫ x : Real,
          guinandWeilPiPolynomialGaussianSource p (x : Complex) *
            Complex.exp (-Complex.I * (u : Complex) * (x : Complex)) := by
      rw [hshift]

/--
Horizontal contour shift in mathlib's exact Fourier normalization.  The
frequency `u` in `exp (-I*u*x)` is sampled at `u / (2*pi)` by the Fourier
transform.
-/
theorem integral_guinandWeilPiPolynomialGaussianSource_horizontalLine_mul_exp_eq_fourier
    (p : Polynomial Complex) (u y : Real) :
    (∫ x : Real,
        guinandWeilPiPolynomialGaussianSource p
            ((x : Complex) + (y : Complex) * Complex.I) *
          Complex.exp (-Complex.I * (u : Complex) * (x : Complex))) =
      Complex.exp ((-(u * y) : Real) : Complex) *
        FourierTransform.fourier
          (fun x : Real =>
            guinandWeilPiPolynomialGaussianSource p (x : Complex))
          (u / (2 * Real.pi)) := by
  have hfourier :
      FourierTransform.fourier
        (fun x : Real =>
          guinandWeilPiPolynomialGaussianSource p (x : Complex))
          (u / (2 * Real.pi)) =
        ∫ x : Real,
          guinandWeilPiPolynomialGaussianSource p (x : Complex) *
            Complex.exp (-Complex.I * (u : Complex) * (x : Complex)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul]
    have hexponent :
        ((-2 * Real.pi * x * (u / (2 * Real.pi)) : Real) : Complex) *
            Complex.I =
          -Complex.I * (u : Complex) * (x : Complex) := by
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [hexponent]
    ring
  rw [integral_guinandWeilPiPolynomialGaussianSource_horizontalLine_mul_exp_eq,
    hfourier]

/-- The xi right wall corresponds to the source height `y = -3/4`. -/
theorem integral_guinandWeilPiPolynomialGaussianSource_xiRightLine_mul_exp_eq_fourier
    (p : Polynomial Complex) (u : Real) :
    (∫ x : Real,
        guinandWeilPiPolynomialGaussianSource p
            ((x : Complex) - (3 / 4 : Real) * Complex.I) *
          Complex.exp (-Complex.I * (u : Complex) * (x : Complex))) =
      Complex.exp (((3 / 4 : Real) * u : Real) : Complex) *
        FourierTransform.fourier
          (fun x : Real =>
            guinandWeilPiPolynomialGaussianSource p (x : Complex))
          (u / (2 * Real.pi)) := by
  simpa only [sub_eq_add_neg, neg_mul, ofReal_neg, mul_neg, neg_neg, mul_comm] using
    integral_guinandWeilPiPolynomialGaussianSource_horizontalLine_mul_exp_eq_fourier
      p u (-(3 / 4 : Real))

end

end RiemannHypothesisProject
