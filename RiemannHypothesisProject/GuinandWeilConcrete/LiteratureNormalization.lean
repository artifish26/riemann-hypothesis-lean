import RiemannHypothesisProject.GuinandWeilConcrete.GaussianPrimeSide
import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianZeroSide
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Literature normalization of the concrete Guinand-Weil sides

Mathlib's real Fourier transform uses the character
`exp (-2 * pi * I * x * xi)`.  In that convention the classical zeta
Guinand-Weil formula samples the Fourier transform at
`± log n / (2 * pi)` and multiplies the prime sum by `1 / (2 * pi)`.
The Archimedean term is `1 / pi` times the logarithmic derivative of
Deligne's `GammaR` factor on the critical line.

This file freezes those constants for the polynomial-Gaussian source before
the borrowed zeta explicit-formula proof is formalized.  It deliberately does
not turn the formula identity into a field or an assumption.
-/

namespace RiemannHypothesisProject

open MeasureTheory

noncomputable section

/-- One prime-power contribution in the literature normalization compatible
with Mathlib's `2*pi` Fourier character. -/
def guinandWeilLiteraturePrimeTerm
    (f : SchwartzLineTestFunction) (n : Nat) : Real :=
  - (1 / (2 * Real.pi)) *
    (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
      (((SchwartzLineTestFunction.fourier f)
          (Real.log (n : Real) / (2 * Real.pi))).re +
        ((SchwartzLineTestFunction.fourier f)
          (-Real.log (n : Real) / (2 * Real.pi))).re)

/-- The infinite prime side in the literature normalization. -/
def guinandWeilLiteraturePrimeSide
    (f : SchwartzLineTestFunction) : Real :=
  tsum (guinandWeilLiteraturePrimeTerm f)

/-- The completed-zeta Archimedean side in the literature normalization. -/
def guinandWeilLiteratureGammaSide
    (f : SchwartzLineTestFunction) : Real :=
  (1 / Real.pi) *
    ∫ t : Real, ((f t) * guinandWeilGammaLogDerivative t).re ∂volume

/-- The direct pole contribution for one entire polynomial-Gaussian source. -/
def guinandWeilPiPolynomialGaussianLiteraturePoleSide
    (p : Polynomial Complex) : Real :=
  (guinandWeilPiPolynomialGaussianSource p (riemannWeilZeroArgument 0) +
    guinandWeilPiPolynomialGaussianSource p (riemannWeilZeroArgument 1)).re

/-- The direct completed-zeta zero side for one polynomial-Gaussian source. -/
def guinandWeilPiPolynomialGaussianLiteratureZeroSide
    (p : Polynomial Complex) : Real :=
  tsum (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p)

/-- The literature-normalized residual side for one polynomial-Gaussian. -/
def guinandWeilPiPolynomialGaussianLiteratureResidualSide
    (p : Polynomial Complex) : Real :=
  guinandWeilLiteraturePrimeSide
      (guinandWeilPiPolynomialGaussianSchwartz p) +
    guinandWeilPiPolynomialGaussianLiteraturePoleSide p +
      guinandWeilLiteratureGammaSide
        (guinandWeilPiPolynomialGaussianSchwartz p)

/-- The direct distinct-location source target in the primary-source
normalization.  It is retained as the original normalization surface, but it
does not encode analytic zero multiplicity.  The selected faithful target is
`GuinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula` in the higher
multiplicity formula-handoff module. -/
def GuinandWeilPiPolynomialGaussianLiteratureFormula
    (p : Polynomial Complex) : Prop :=
  guinandWeilPiPolynomialGaussianLiteratureZeroSide p =
    guinandWeilPiPolynomialGaussianLiteratureResidualSide p

/-- Polynomial-Gaussians retain inverse-cube decay at the literature Fourier
samples `± log n / (2*pi)`. -/
theorem exists_pos_const_eventually_norm_guinandWeilPiPolynomialGaussianSource_log_div_two_pi_le_const_div_cube
    (p : Polynomial Complex) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in Filter.atTop,
        norm (guinandWeilPiPolynomialGaussianSource p
          ((Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) <=
            C / (n : Real) ^ 3 ∧
        norm (guinandWeilPiPolynomialGaussianSource p
          ((-Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) <=
            C / (n : Real) ^ 3 := by
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow p with
    ⟨B, hB, hpolynomial⟩
  let d : Nat := p.natDegree
  refine ⟨B * 3 ^ d, mul_pos hB (by positivity), ?_⟩
  have hlog :
      Filter.Tendsto (fun n : Nat => Real.log (n : Real))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := Real))
  filter_upwards
      [hlog.eventually_ge_atTop
        (4 * Real.pi * ((d : Real) + 3)),
        Filter.eventually_ge_atTop (1 : Nat)] with n hnlog hn
  have hn_real : 1 <= (n : Real) := by exact_mod_cast hn
  have hn_pos : 0 < (n : Real) := zero_lt_one.trans_le hn_real
  have hlog_nonneg : 0 <= Real.log (n : Real) := Real.log_nonneg hn_real
  have htwo_pi_pos : 0 < 2 * Real.pi := by positivity
  have htwo_pi_one : 1 <= 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hscaled_nonneg :
      0 <= Real.log (n : Real) / (2 * Real.pi) :=
    div_nonneg hlog_nonneg htwo_pi_pos.le
  have hscaled_le_n :
      Real.log (n : Real) / (2 * Real.pi) <= (n : Real) := by
    exact
      (div_le_self hlog_nonneg htwo_pi_one).trans
        (Real.log_le_self (Nat.cast_nonneg n))
  have hradius_pos :
      norm ((Real.log (n : Real) / (2 * Real.pi) : Real) : Complex) + 2 <=
        3 * (n : Real) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscaled_nonneg]
    nlinarith
  have hradius_neg :
      norm ((-Real.log (n : Real) / (2 * Real.pi) : Real) : Complex) + 2 <=
        3 * (n : Real) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_nonneg hlog_nonneg, abs_of_pos htwo_pi_pos]
    nlinarith
  have hquad :
      4 * Real.pi * ((d : Real) + 3) * Real.log (n : Real) <=
        Real.log (n : Real) ^ 2 := by
    simpa [pow_two] using
      mul_le_mul_of_nonneg_right hnlog hlog_nonneg
  have hdiv :
      ((d : Real) + 3) * Real.log (n : Real) <=
        Real.log (n : Real) ^ 2 / (4 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * Real.pi)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hquad
  have hexponent :
      -Real.pi * (Real.log (n : Real) / (2 * Real.pi)) ^ 2 <=
        -((d : Real) + 3) * Real.log (n : Real) := by
    have heq :
        -Real.pi * (Real.log (n : Real) / (2 * Real.pi)) ^ 2 =
          -(Real.log (n : Real) ^ 2 / (4 * Real.pi)) := by
      field_simp [Real.pi_ne_zero]
      ring
    rw [heq]
    linarith
  have hgaussian :
      Real.exp
          (-Real.pi * (Real.log (n : Real) / (2 * Real.pi)) ^ 2) <=
        1 / (n : Real) ^ (d + 3) := by
    calc
      Real.exp
          (-Real.pi * (Real.log (n : Real) / (2 * Real.pi)) ^ 2) <=
          Real.exp (-((d : Real) + 3) * Real.log (n : Real)) :=
        Real.exp_le_exp.mpr hexponent
      _ = 1 / (n : Real) ^ (d + 3) := by
        rw [show -((d : Real) + 3) * Real.log (n : Real) =
          -((d + 3 : Nat) * Real.log (n : Real)) by
            push_cast
            ring]
        rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn_pos]
        simp [one_div]
  have hpolynomial_pos :
      norm (p.aeval
          ((Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) <=
        B * (3 * (n : Real)) ^ d := by
    calc
      norm (p.aeval
          ((Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) <=
          B *
            (norm
                ((Real.log (n : Real) / (2 * Real.pi) : Real) : Complex) + 2) ^
              p.natDegree := hpolynomial _
      _ <= B * (3 * (n : Real)) ^ d := by
        dsimp [d]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hradius_pos _) hB.le
  have hpolynomial_neg :
      norm (p.aeval
          ((-Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) <=
        B * (3 * (n : Real)) ^ d := by
    calc
      norm (p.aeval
          ((-Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) <=
          B *
            (norm
                ((-Real.log (n : Real) / (2 * Real.pi) : Real) : Complex) + 2) ^
              p.natDegree := hpolynomial _
      _ <= B * (3 * (n : Real)) ^ d := by
        dsimp [d]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hradius_neg _) hB.le
  constructor
  · rw [guinandWeilPiPolynomialGaussianSource, norm_mul]
    calc
      norm (p.aeval
          ((Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) *
          norm (guinandWeilPiGaussianSource
            ((Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) <=
          (B * (3 * (n : Real)) ^ d) *
            Real.exp
              (-Real.pi *
                (Real.log (n : Real) / (2 * Real.pi)) ^ 2) := by
        apply mul_le_mul hpolynomial_pos
        · exact le_of_eq (by
            simpa using
              norm_guinandWeilPiGaussianSource_horizontalLine
                (Real.log (n : Real) / (2 * Real.pi)) 0)
        · exact norm_nonneg _
        · positivity
      _ <= (B * (3 * (n : Real)) ^ d) *
          (1 / (n : Real) ^ (d + 3)) :=
        mul_le_mul_of_nonneg_left hgaussian (by positivity)
      _ = (B * 3 ^ d) / (n : Real) ^ 3 := by
        field_simp [pow_add, mul_pow]
        ring
  · rw [guinandWeilPiPolynomialGaussianSource, norm_mul]
    calc
      norm (p.aeval
          ((-Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) *
          norm (guinandWeilPiGaussianSource
            ((-Real.log (n : Real) / (2 * Real.pi) : Real) : Complex)) <=
          (B * (3 * (n : Real)) ^ d) *
            Real.exp
              (-Real.pi *
                (Real.log (n : Real) / (2 * Real.pi)) ^ 2) := by
        apply mul_le_mul hpolynomial_neg
        · exact le_of_eq (by
            have hnorm :=
              norm_guinandWeilPiGaussianSource_horizontalLine
                (-Real.log (n : Real) / (2 * Real.pi)) 0
            rw [show
              (-Real.log (n : Real) / (2 * Real.pi)) ^ 2 =
                (Real.log (n : Real) / (2 * Real.pi)) ^ 2 by ring] at hnorm
            simpa using hnorm)
        · exact norm_nonneg _
        · positivity
      _ <= (B * (3 * (n : Real)) ^ d) *
          (1 / (n : Real) ^ (d + 3)) :=
        mul_le_mul_of_nonneg_left hgaussian (by positivity)
      _ = (B * 3 ^ d) / (n : Real) ^ 3 := by
        field_simp [pow_add, mul_pow]
        ring

/-- The Fourier transform of every polynomial-Gaussian has the same
inverse-cube bound at the literature prime samples. -/
theorem exists_pos_const_eventually_norm_fourier_guinandWeilPiPolynomialGaussianSchwartz_log_div_two_pi_le_const_div_cube
    (p : Polynomial Complex) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in Filter.atTop,
        norm (SchwartzLineTestFunction.fourier
          (guinandWeilPiPolynomialGaussianSchwartz p)
          (Real.log (n : Real) / (2 * Real.pi))) <=
            C / (n : Real) ^ 3 ∧
        norm (SchwartzLineTestFunction.fourier
          (guinandWeilPiPolynomialGaussianSchwartz p)
          (-Real.log (n : Real) / (2 * Real.pi))) <=
            C / (n : Real) ^ 3 := by
  let q := guinandWeilPiPolynomialGaussianFourierPolynomial p
  rcases
      exists_pos_const_eventually_norm_guinandWeilPiPolynomialGaussianSource_log_div_two_pi_le_const_div_cube
        q with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with n hn
  rw [fourier_guinandWeilPiPolynomialGaussianSchwartz p]
  exact hn

/-- The correctly normalized polynomial-Gaussian prime term has an eventual
inverse-square majorant. -/
theorem exists_pos_const_eventually_norm_guinandWeilLiteraturePrimeTerm_guinandWeilPiPolynomialGaussianSchwartz_le_const_div_sq
    (p : Polynomial Complex) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in Filter.atTop,
        norm (guinandWeilLiteraturePrimeTerm
          (guinandWeilPiPolynomialGaussianSchwartz p) n) <=
            C / (n : Real) ^ 2 := by
  rcases
      exists_pos_const_eventually_norm_fourier_guinandWeilPiPolynomialGaussianSchwartz_log_div_two_pi_le_const_div_cube
        p with
    ⟨C, hC, hfourier⟩
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  filter_upwards
      [hfourier, Filter.eventually_ge_atTop (1 : Nat)] with n hfourier_n hn
  have hn_real : 1 <= (n : Real) := by exact_mod_cast hn
  have hn_pos : 0 < (n : Real) := zero_lt_one.trans_le hn_real
  have hsqrt : 1 <= Real.sqrt (n : Real) :=
    Real.one_le_sqrt.mpr hn_real
  have hlambda_nonneg :
      0 <= ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hlambda_le :
      ArithmeticFunction.vonMangoldt n <= (n : Real) :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_self (Nat.cast_nonneg n))
  have hcoeff_nonneg :
      0 <= ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) :=
    div_nonneg hlambda_nonneg (Real.sqrt_nonneg _)
  have hcoeff_le :
      ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) <=
        (n : Real) := by
    calc
      ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) <=
          ArithmeticFunction.vonMangoldt n :=
        div_le_self hlambda_nonneg hsqrt
      _ <= (n : Real) := hlambda_le
  have hsum :
      |((SchwartzLineTestFunction.fourier
          (guinandWeilPiPolynomialGaussianSchwartz p)
          (Real.log (n : Real) / (2 * Real.pi))).re +
        (SchwartzLineTestFunction.fourier
          (guinandWeilPiPolynomialGaussianSchwartz p)
          (-Real.log (n : Real) / (2 * Real.pi))).re)| <=
        (2 * C) / (n : Real) ^ 3 := by
    calc
      |((SchwartzLineTestFunction.fourier
          (guinandWeilPiPolynomialGaussianSchwartz p)
          (Real.log (n : Real) / (2 * Real.pi))).re +
        (SchwartzLineTestFunction.fourier
          (guinandWeilPiPolynomialGaussianSchwartz p)
          (-Real.log (n : Real) / (2 * Real.pi))).re)| <=
          norm (SchwartzLineTestFunction.fourier
            (guinandWeilPiPolynomialGaussianSchwartz p)
            (Real.log (n : Real) / (2 * Real.pi))) +
          norm (SchwartzLineTestFunction.fourier
            (guinandWeilPiPolynomialGaussianSchwartz p)
            (-Real.log (n : Real) / (2 * Real.pi))) := by
        exact (abs_add_le _ _).trans
          (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))
      _ <= C / (n : Real) ^ 3 + C / (n : Real) ^ 3 :=
        add_le_add hfourier_n.1 hfourier_n.2
      _ = (2 * C) / (n : Real) ^ 3 := by ring
  have hcore :
      (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
          |((SchwartzLineTestFunction.fourier
              (guinandWeilPiPolynomialGaussianSchwartz p)
              (Real.log (n : Real) / (2 * Real.pi))).re +
            (SchwartzLineTestFunction.fourier
              (guinandWeilPiPolynomialGaussianSchwartz p)
              (-Real.log (n : Real) / (2 * Real.pi))).re)| <=
        (2 * C) / (n : Real) ^ 2 := by
    calc
      (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
          |((SchwartzLineTestFunction.fourier
              (guinandWeilPiPolynomialGaussianSchwartz p)
              (Real.log (n : Real) / (2 * Real.pi))).re +
            (SchwartzLineTestFunction.fourier
              (guinandWeilPiPolynomialGaussianSchwartz p)
              (-Real.log (n : Real) / (2 * Real.pi))).re)| <=
          (n : Real) * ((2 * C) / (n : Real) ^ 3) :=
        mul_le_mul hcoeff_le hsum (abs_nonneg _) (Nat.cast_nonneg n)
      _ = (2 * C) / (n : Real) ^ 2 := by field_simp
  have hscale_nonneg : 0 <= 1 / (2 * Real.pi) := by positivity
  have hscale_le_one : 1 / (2 * Real.pi) <= 1 := by
    rw [div_le_one (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.pi_gt_three]
  have hcore_nonneg :
      0 <=
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
          |((SchwartzLineTestFunction.fourier
              (guinandWeilPiPolynomialGaussianSchwartz p)
              (Real.log (n : Real) / (2 * Real.pi))).re +
            (SchwartzLineTestFunction.fourier
              (guinandWeilPiPolynomialGaussianSchwartz p)
              (-Real.log (n : Real) / (2 * Real.pi))).re)| :=
    mul_nonneg hcoeff_nonneg (abs_nonneg _)
  unfold guinandWeilLiteraturePrimeTerm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg hscale_nonneg, abs_of_nonneg hcoeff_nonneg]
  calc
    (1 / (2 * Real.pi)) *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
          |((SchwartzLineTestFunction.fourier
              (guinandWeilPiPolynomialGaussianSchwartz p)
              (Real.log (n : Real) / (2 * Real.pi))).re +
            (SchwartzLineTestFunction.fourier
              (guinandWeilPiPolynomialGaussianSchwartz p)
              (-Real.log (n : Real) / (2 * Real.pi))).re)| =
        (1 / (2 * Real.pi)) *
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
            |((SchwartzLineTestFunction.fourier
                (guinandWeilPiPolynomialGaussianSchwartz p)
                (Real.log (n : Real) / (2 * Real.pi))).re +
              (SchwartzLineTestFunction.fourier
                (guinandWeilPiPolynomialGaussianSchwartz p)
                (-Real.log (n : Real) / (2 * Real.pi))).re)|) := by ring
    _ <= 1 * ((2 * C) / (n : Real) ^ 2) :=
      mul_le_mul hscale_le_one hcore hcore_nonneg zero_le_one
    _ = (2 * C) / (n : Real) ^ 2 := one_mul _

/-- Absolute convergence of the correctly normalized polynomial-Gaussian
prime side. -/
theorem summable_norm_guinandWeilLiteraturePrimeTerm_guinandWeilPiPolynomialGaussianSchwartz
    (p : Polynomial Complex) :
    Summable (fun n : Nat =>
      norm (guinandWeilLiteraturePrimeTerm
        (guinandWeilPiPolynomialGaussianSchwartz p) n)) := by
  rcases
      exists_pos_const_eventually_norm_guinandWeilLiteraturePrimeTerm_guinandWeilPiPolynomialGaussianSchwartz_le_const_div_sq
        p with
    ⟨C, _hC, hbound⟩
  have hmajorant : Summable (fun n : Nat => C / (n : Real) ^ 2) := by
    have hbase : Summable (fun n : Nat => 1 / (n : Real) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa [div_eq_mul_inv] using hbase.mul_left C
  exact hmajorant.of_norm_bounded_eventually_nat (by
    filter_upwards [hbound] with n hn
    simpa [Real.norm_of_nonneg (norm_nonneg _)] using hn)

/-- Signed convergence of the correctly normalized polynomial-Gaussian prime
side. -/
theorem summable_guinandWeilLiteraturePrimeTerm_guinandWeilPiPolynomialGaussianSchwartz
    (p : Polynomial Complex) :
    Summable (guinandWeilLiteraturePrimeTerm
      (guinandWeilPiPolynomialGaussianSchwartz p)) :=
  (summable_norm_guinandWeilLiteraturePrimeTerm_guinandWeilPiPolynomialGaussianSchwartz
    p).of_norm

/-- The legacy gamma coefficient is exactly `-1/2` of the literature
coefficient.  This formally exposes the normalization mismatch. -/
theorem guinandWeilLiteratureGammaSide_eq_neg_two_mul_guinandWeilGammaSide
    (f : SchwartzLineTestFunction) :
    guinandWeilLiteratureGammaSide f = -2 * guinandWeilGammaSide f := by
  unfold guinandWeilLiteratureGammaSide guinandWeilGammaSide
  field_simp [Real.pi_ne_zero]

/-- The literature pole arguments are precisely `+i/2` and `-i/2`. -/
theorem guinandWeilPiPolynomialGaussianLiteraturePoleSide_eq
    (p : Polynomial Complex) :
    guinandWeilPiPolynomialGaussianLiteraturePoleSide p =
      (guinandWeilPiPolynomialGaussianSource p (Complex.I / 2) +
        guinandWeilPiPolynomialGaussianSource p (-Complex.I / 2)).re := by
  have hzero : riemannWeilZeroArgument 0 = Complex.I / 2 := by
    unfold riemannWeilZeroArgument
    field_simp [Complex.I_ne_zero]
    simp [pow_two, Complex.I_mul_I]
  have hone : riemannWeilZeroArgument 1 = -Complex.I / 2 := by
    unfold riemannWeilZeroArgument
    field_simp [Complex.I_ne_zero]
    norm_num [pow_two, Complex.I_mul_I]
  simp [guinandWeilPiPolynomialGaussianLiteraturePoleSide, hzero, hone]

/-- The direct literature zero side is absolutely defined whenever the
separate polynomial zero-counting input is supplied. -/
theorem summable_guinandWeilPiPolynomialGaussianLiteratureZeroSide
    (p : Polynomial Complex)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (k : Nat)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real)) :
    Summable (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p) :=
  summable_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight
    p counting counting_cutoff_eq k growth_add_one_lt_k

end

end RiemannHypothesisProject
