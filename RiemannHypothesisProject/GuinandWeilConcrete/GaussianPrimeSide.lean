import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianFourierSource
import RiemannHypothesisProject.GuinandWeilConcrete.PrimeCutoff

/-!
# Gaussian source estimates for the concrete Guinand-Weil prime side

The `pi`-normalized Gaussian is self-Fourier.  Sampling it at `log n` therefore
has super-polynomial decay in `n`; this module turns that decay into absolute
summability of the concrete von-Mangoldt prime side without a compact Fourier
support hypothesis.
-/

namespace RiemannHypothesisProject

open Filter
open scoped FourierTransform Topology

noncomputable section

/-- The `pi`-normalized Gaussian as an actual project Schwartz test. -/
noncomputable def guinandWeilPiGaussianSchwartz : SchwartzLineTestFunction :=
  guinandWeilPiPolynomialGaussianSchwartz 1

@[simp]
theorem guinandWeilPiGaussianSchwartz_apply
    (x : Real) :
    guinandWeilPiGaussianSchwartz x =
      guinandWeilPiGaussianSource (x : Complex) := by
  simp [guinandWeilPiGaussianSchwartz,
    guinandWeilPiPolynomialGaussianSchwartz_apply,
    guinandWeilPiPolynomialGaussianSource]

/-- The project Fourier transform of the Gaussian Schwartz test is itself. -/
theorem fourier_guinandWeilPiGaussianSchwartz_apply
    (t : Real) :
    SchwartzLineTestFunction.fourier guinandWeilPiGaussianSchwartz t =
      guinandWeilPiGaussianSource (t : Complex) := by
  unfold SchwartzLineTestFunction.fourier
  rw [SchwartzMap.fourier_coe]
  rw [show (⇑guinandWeilPiGaussianSchwartz : Real -> Complex) =
      fun x : Real => guinandWeilPiGaussianSource (x : Complex) by
    funext x
    exact guinandWeilPiGaussianSchwartz_apply x]
  change
    (𝓕 fun x : Real => guinandWeilPiGaussianSource (x : Complex)) t =
      guinandWeilPiGaussianSource (t : Complex)
  exact congrFun fourier_guinandWeilPiGaussianSource_real t

/--
At logarithmic prime samples, the self-Fourier Gaussian is eventually bounded
by `n⁻³`.  The exponent three is deliberately stronger than needed so the
von-Mangoldt coefficient can be handled by the elementary bound `Λ(n) ≤ n`.
-/
theorem eventually_norm_fourier_guinandWeilPiGaussianSchwartz_log_le_inv_cube :
    ∀ᶠ n : Nat in atTop,
      norm (SchwartzLineTestFunction.fourier
        guinandWeilPiGaussianSchwartz (Real.log (n : Real))) <=
          1 / (n : Real) ^ 3 ∧
      norm (SchwartzLineTestFunction.fourier
        guinandWeilPiGaussianSchwartz (-Real.log (n : Real))) <=
          1 / (n : Real) ^ 3 := by
  have hlog :
      Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := Real))
  filter_upwards
      [hlog.eventually_ge_atTop (3 / Real.pi),
        eventually_ge_atTop (1 : Nat)] with n hnlog hn
  have hn_real : 1 <= (n : Real) := by exact_mod_cast hn
  have hn_pos : 0 < (n : Real) := zero_lt_one.trans_le hn_real
  have hlog_nonneg : 0 <= Real.log (n : Real) :=
    Real.log_nonneg hn_real
  have hexponent :
      -Real.pi * Real.log (n : Real) ^ 2 <=
        -3 * Real.log (n : Real) := by
    have hpi_log : 3 <= Real.pi * Real.log (n : Real) := by
      have := (div_le_iff₀ Real.pi_pos).mp hnlog
      simpa [mul_comm] using this
    nlinarith
  have hdecay :
      Real.exp (-Real.pi * Real.log (n : Real) ^ 2) <=
        1 / (n : Real) ^ 3 := by
    calc
      Real.exp (-Real.pi * Real.log (n : Real) ^ 2) <=
          Real.exp (-3 * Real.log (n : Real)) :=
        Real.exp_le_exp.mpr hexponent
      _ = 1 / (n : Real) ^ 3 := by
        rw [show -3 * Real.log (n : Real) =
          -(3 * Real.log (n : Real)) by ring]
        rw [Real.exp_neg]
        rw [show 3 * Real.log (n : Real) =
          (3 : Nat) * Real.log (n : Real) by norm_num]
        rw [Real.exp_nat_mul, Real.exp_log hn_pos]
        simp [one_div]
  constructor
  · rw [fourier_guinandWeilPiGaussianSchwartz_apply]
    calc
      norm (guinandWeilPiGaussianSource
          (Real.log (n : Real) : Complex)) =
          Real.exp (-Real.pi * Real.log (n : Real) ^ 2) := by
        simpa using
          norm_guinandWeilPiGaussianSource_horizontalLine
            (Real.log (n : Real)) 0
      _ <= 1 / (n : Real) ^ 3 := hdecay
  · rw [fourier_guinandWeilPiGaussianSchwartz_apply]
    calc
      norm (guinandWeilPiGaussianSource
          ((-Real.log (n : Real) : Real) : Complex)) =
          Real.exp (-Real.pi * Real.log (n : Real) ^ 2) := by
        simpa using
          norm_guinandWeilPiGaussianSource_horizontalLine
            (-Real.log (n : Real)) 0
      _ <= 1 / (n : Real) ^ 3 := hdecay

/--
An eventual `C * n⁻³` bound at both logarithmic Fourier samples gives an
eventual `2C * n⁻²` bound for the concrete von-Mangoldt prime summand.
-/
theorem eventually_norm_guinandWeilPrimeTerm_le_two_mul_const_div_sq_of_fourier_log_le_const_div_cube
    (f : SchwartzLineTestFunction) (C : Real)
    (hfourier :
      ∀ᶠ n : Nat in atTop,
        norm (SchwartzLineTestFunction.fourier f (Real.log (n : Real))) <=
            C / (n : Real) ^ 3 ∧
        norm (SchwartzLineTestFunction.fourier f (-Real.log (n : Real))) <=
            C / (n : Real) ^ 3) :
    ∀ᶠ n : Nat in atTop,
      norm (guinandWeilPrimeTerm f n) <= (2 * C) / (n : Real) ^ 2 := by
  filter_upwards
      [hfourier, eventually_ge_atTop (1 : Nat)] with n hfourier_n hn
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
          f (Real.log (n : Real))).re +
        (SchwartzLineTestFunction.fourier
          f (-Real.log (n : Real))).re)| <=
        (2 * C) / (n : Real) ^ 3 := by
    calc
      |((SchwartzLineTestFunction.fourier
          f (Real.log (n : Real))).re +
        (SchwartzLineTestFunction.fourier
          f (-Real.log (n : Real))).re)| <=
          norm (SchwartzLineTestFunction.fourier
            f (Real.log (n : Real))) +
          norm (SchwartzLineTestFunction.fourier
            f (-Real.log (n : Real))) := by
        exact (abs_add_le _ _).trans
          (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))
      _ <= C / (n : Real) ^ 3 + C / (n : Real) ^ 3 :=
        add_le_add hfourier_n.1 hfourier_n.2
      _ = (2 * C) / (n : Real) ^ 3 := by ring
  unfold guinandWeilPrimeTerm
  rw [Real.norm_eq_abs]
  rw [abs_mul, abs_neg, abs_of_nonneg hcoeff_nonneg]
  calc
    (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
        |((SchwartzLineTestFunction.fourier
            f (Real.log (n : Real))).re +
          (SchwartzLineTestFunction.fourier
            f (-Real.log (n : Real))).re)| <=
      (n : Real) * ((2 * C) / (n : Real) ^ 3) :=
        mul_le_mul hcoeff_le hsum (abs_nonneg _) (Nat.cast_nonneg n)
    _ = (2 * C) / (n : Real) ^ 2 := by field_simp

/--
An eventual `C * n⁻³` bound at both logarithmic Fourier samples makes the
concrete von-Mangoldt prime side absolutely summable.
-/
theorem summable_norm_guinandWeilPrimeTerm_of_eventually_fourier_log_le_const_div_cube
    (f : SchwartzLineTestFunction) (C : Real)
    (hfourier :
      ∀ᶠ n : Nat in atTop,
        norm (SchwartzLineTestFunction.fourier f (Real.log (n : Real))) <=
            C / (n : Real) ^ 3 ∧
        norm (SchwartzLineTestFunction.fourier f (-Real.log (n : Real))) <=
            C / (n : Real) ^ 3) :
    Summable (fun n : Nat =>
      norm (guinandWeilPrimeTerm f n)) := by
  have hmajorant : Summable (fun n : Nat => (2 * C) / (n : Real) ^ 2) := by
    have hbase : Summable (fun n : Nat => 1 / (n : Real) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa [div_eq_mul_inv] using hbase.mul_left (2 * C)
  refine hmajorant.of_norm_bounded_eventually_nat ?_
  filter_upwards
      [eventually_norm_guinandWeilPrimeTerm_le_two_mul_const_div_sq_of_fourier_log_le_const_div_cube
        f C hfourier] with n hn
  simpa [Real.norm_of_nonneg (norm_nonneg _)] using hn

/--
The concrete von-Mangoldt prime side is absolutely summable for the
`pi`-normalized Gaussian source.  This is a genuine source-class estimate and
does not use compact Fourier support or eventual vanishing of prime terms.
-/
theorem summable_norm_guinandWeilPrimeTerm_guinandWeilPiGaussianSchwartz :
    Summable (fun n : Nat =>
      norm (guinandWeilPrimeTerm guinandWeilPiGaussianSchwartz n)) :=
  summable_norm_guinandWeilPrimeTerm_of_eventually_fourier_log_le_const_div_cube
    guinandWeilPiGaussianSchwartz 1
    (by
      simpa using
        eventually_norm_fourier_guinandWeilPiGaussianSchwartz_log_le_inv_cube)

/-- The concrete Gaussian prime summand itself is summable. -/
theorem summable_guinandWeilPrimeTerm_guinandWeilPiGaussianSchwartz :
    Summable (fun n : Nat =>
      guinandWeilPrimeTerm guinandWeilPiGaussianSchwartz n) :=
  summable_norm_guinandWeilPrimeTerm_guinandWeilPiGaussianSchwartz.of_norm

/--
Every polynomial-Gaussian has a uniform `C * n⁻³` bound at the positive and
negative logarithmic samples.  The proof keeps the polynomial growth explicit
and spends additional Gaussian decay according to the polynomial degree.
-/
theorem exists_pos_const_eventually_norm_guinandWeilPiPolynomialGaussianSource_log_le_const_div_cube
    (p : Polynomial Complex) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in atTop,
        norm (guinandWeilPiPolynomialGaussianSource p
          (Real.log (n : Real) : Complex)) <= C / (n : Real) ^ 3 ∧
        norm (guinandWeilPiPolynomialGaussianSource p
          ((-Real.log (n : Real) : Real) : Complex)) <= C / (n : Real) ^ 3 := by
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow p with
    ⟨B, hB, hpolynomial⟩
  let d : Nat := p.natDegree
  refine ⟨B * 3 ^ d, mul_pos hB (by positivity), ?_⟩
  have hlog :
      Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := Real))
  filter_upwards
      [hlog.eventually_ge_atTop (((d : Real) + 3) / Real.pi),
        eventually_ge_atTop (1 : Nat)] with n hnlog hn
  have hn_real : 1 <= (n : Real) := by exact_mod_cast hn
  have hn_pos : 0 < (n : Real) := zero_lt_one.trans_le hn_real
  have hlog_nonneg : 0 <= Real.log (n : Real) :=
    Real.log_nonneg hn_real
  have hlog_le : Real.log (n : Real) <= (n : Real) :=
    Real.log_le_self (Nat.cast_nonneg n)
  have hradius_pos :
      norm (Real.log (n : Real) : Complex) + 2 <= 3 * (n : Real) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
    nlinarith
  have hradius_neg :
      norm ((-Real.log (n : Real) : Real) : Complex) + 2 <=
        3 * (n : Real) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg hlog_nonneg]
    nlinarith
  have hpi_log :
      (d : Real) + 3 <= Real.pi * Real.log (n : Real) := by
    have := (div_le_iff₀ Real.pi_pos).mp hnlog
    simpa [mul_comm] using this
  have hexponent :
      -Real.pi * Real.log (n : Real) ^ 2 <=
        -((d : Real) + 3) * Real.log (n : Real) := by
    nlinarith
  have hgaussian :
      Real.exp (-Real.pi * Real.log (n : Real) ^ 2) <=
        1 / (n : Real) ^ (d + 3) := by
    calc
      Real.exp (-Real.pi * Real.log (n : Real) ^ 2) <=
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
      norm (p.aeval (Real.log (n : Real) : Complex)) <=
        B * (3 * (n : Real)) ^ d := by
    calc
      norm (p.aeval (Real.log (n : Real) : Complex)) <=
          B * (norm (Real.log (n : Real) : Complex) + 2) ^ p.natDegree :=
        hpolynomial _
      _ <= B * (3 * (n : Real)) ^ d := by
        dsimp [d]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hradius_pos _) hB.le
  have hpolynomial_neg :
      norm (p.aeval ((-Real.log (n : Real) : Real) : Complex)) <=
        B * (3 * (n : Real)) ^ d := by
    calc
      norm (p.aeval ((-Real.log (n : Real) : Real) : Complex)) <=
          B * (norm ((-Real.log (n : Real) : Real) : Complex) + 2) ^
            p.natDegree := hpolynomial _
      _ <= B * (3 * (n : Real)) ^ d := by
        dsimp [d]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hradius_neg _) hB.le
  constructor
  · rw [guinandWeilPiPolynomialGaussianSource, norm_mul]
    calc
      norm (p.aeval (Real.log (n : Real) : Complex)) *
          norm (guinandWeilPiGaussianSource
            (Real.log (n : Real) : Complex)) <=
          (B * (3 * (n : Real)) ^ d) *
            Real.exp (-Real.pi * Real.log (n : Real) ^ 2) := by
        apply mul_le_mul hpolynomial_pos
        · exact le_of_eq (by
            simpa using
              norm_guinandWeilPiGaussianSource_horizontalLine
                (Real.log (n : Real)) 0)
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
      norm (p.aeval ((-Real.log (n : Real) : Real) : Complex)) *
          norm (guinandWeilPiGaussianSource
            ((-Real.log (n : Real) : Real) : Complex)) <=
          (B * (3 * (n : Real)) ^ d) *
            Real.exp (-Real.pi * Real.log (n : Real) ^ 2) := by
        apply mul_le_mul hpolynomial_neg
        · exact le_of_eq (by
            simpa using
              norm_guinandWeilPiGaussianSource_horizontalLine
                (-Real.log (n : Real)) 0)
        · exact norm_nonneg _
        · positivity
      _ <= (B * (3 * (n : Real)) ^ d) *
          (1 / (n : Real) ^ (d + 3)) :=
        mul_le_mul_of_nonneg_left hgaussian (by positivity)
      _ = (B * 3 ^ d) / (n : Real) ^ 3 := by
        field_simp [pow_add, mul_pow]
        ring

/--
Every polynomial-Gaussian project test has logarithmic Fourier samples bounded
by `C * n⁻³` for some positive source-dependent constant.
-/
theorem exists_pos_const_eventually_norm_fourier_guinandWeilPiPolynomialGaussianSchwartz_log_le_const_div_cube
    (p : Polynomial Complex) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in atTop,
        norm (SchwartzLineTestFunction.fourier
          (guinandWeilPiPolynomialGaussianSchwartz p)
          (Real.log (n : Real))) <= C / (n : Real) ^ 3 ∧
        norm (SchwartzLineTestFunction.fourier
          (guinandWeilPiPolynomialGaussianSchwartz p)
          (-Real.log (n : Real))) <= C / (n : Real) ^ 3 := by
  let q := guinandWeilPiPolynomialGaussianFourierPolynomial p
  rcases
      exists_pos_const_eventually_norm_guinandWeilPiPolynomialGaussianSource_log_le_const_div_cube
        q with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with n hn
  have hfourier := fourier_guinandWeilPiPolynomialGaussianSchwartz p
  constructor
  · rw [hfourier]
    exact hn.1
  · rw [hfourier]
    exact hn.2

/--
Every polynomial-Gaussian concrete prime summand has an eventual
source-dependent inverse-square majorant.
-/
theorem exists_pos_const_eventually_norm_guinandWeilPrimeTerm_guinandWeilPiPolynomialGaussianSchwartz_le_const_div_sq
    (p : Polynomial Complex) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in atTop,
        norm (guinandWeilPrimeTerm
          (guinandWeilPiPolynomialGaussianSchwartz p) n) <=
            C / (n : Real) ^ 2 := by
  rcases
      exists_pos_const_eventually_norm_fourier_guinandWeilPiPolynomialGaussianSchwartz_log_le_const_div_cube
        p with ⟨C, hC, hbound⟩
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  exact
    eventually_norm_guinandWeilPrimeTerm_le_two_mul_const_div_sq_of_fourier_log_le_const_div_cube
      (guinandWeilPiPolynomialGaussianSchwartz p) C hbound

/--
The concrete von-Mangoldt prime side is absolutely summable for every member
of the polynomial-Gaussian source family.
-/
theorem summable_norm_guinandWeilPrimeTerm_guinandWeilPiPolynomialGaussianSchwartz
    (p : Polynomial Complex) :
    Summable (fun n : Nat =>
      norm (guinandWeilPrimeTerm
        (guinandWeilPiPolynomialGaussianSchwartz p) n)) := by
  rcases
      exists_pos_const_eventually_norm_fourier_guinandWeilPiPolynomialGaussianSchwartz_log_le_const_div_cube
        p with ⟨C, _hC, hbound⟩
  exact
    summable_norm_guinandWeilPrimeTerm_of_eventually_fourier_log_le_const_div_cube
      (guinandWeilPiPolynomialGaussianSchwartz p) C hbound

/-- Every polynomial-Gaussian concrete prime summand is summable. -/
theorem summable_guinandWeilPrimeTerm_guinandWeilPiPolynomialGaussianSchwartz
    (p : Polynomial Complex) :
    Summable (fun n : Nat =>
      guinandWeilPrimeTerm
        (guinandWeilPiPolynomialGaussianSchwartz p) n) :=
  (summable_norm_guinandWeilPrimeTerm_guinandWeilPiPolynomialGaussianSchwartz
    p).of_norm

end

end RiemannHypothesisProject
