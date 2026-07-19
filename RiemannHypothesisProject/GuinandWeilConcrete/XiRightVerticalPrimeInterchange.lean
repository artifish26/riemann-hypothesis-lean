import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannHypothesisProject.GuinandWeilConcrete.LiteratureNormalization
import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianContourShift
import RiemannHypothesisProject.GuinandWeilConcrete.XiRightVertical

/-!
# Von Mangoldt interchange on the xi right vertical

This module justifies exchanging the complete right-line integral with the
absolutely convergent von Mangoldt L-series.  The majorant uses the exact
`re s = 5/4` term norm and the proved integrability of the shifted
polynomial-Gaussian source.
-/

namespace RiemannHypothesisProject

open Complex Filter MeasureTheory

noncomputable section

private def vonMangoldtComplex (n : Nat) : Complex :=
  (ArithmeticFunction.vonMangoldt n : Complex)

/-- One von Mangoldt L-series term multiplied by the shifted right-line source. -/
noncomputable def guinandWeilXiRightPrimeIntegrand
    (p : Polynomial Complex) (n : Nat) (t : Real) : Complex :=
  guinandWeilPiPolynomialGaussianSource p
      ((t : Complex) - (3 / 4 : Real) * Complex.I) *
    LSeries.term vonMangoldtComplex
      ((5 / 4 : Real) + (t : Complex) * Complex.I) n

/--
One right-line von Mangoldt term evaluates at the exact Fourier sample, with
the contour shift reducing the real exponent from `-5/4` to `-1/2`.
-/
theorem integral_guinandWeilXiRightPrimeIntegrand_eq_fourier
    (p : Polynomial Complex) (n : Nat) :
    (∫ t : Real, guinandWeilXiRightPrimeIntegrand p n t) =
      (ArithmeticFunction.vonMangoldt n : Complex) *
        Complex.exp ((-(1 / 2 : Real) * Real.log (n : Real) : Real) : Complex) *
          FourierTransform.fourier
            (fun x : Real =>
              guinandWeilPiPolynomialGaussianSource p (x : Complex))
            (Real.log (n : Real) / (2 * Real.pi)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [guinandWeilXiRightPrimeIntegrand, vonMangoldtComplex]
  · have hncast : (n : Complex) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hterm (t : Real) :
        LSeries.term vonMangoldtComplex
            ((5 / 4 : Real) + (t : Complex) * Complex.I) n =
          (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp
              ((-(5 / 4 : Real) * Real.log (n : Real) : Real) : Complex) *
            Complex.exp
              (-Complex.I * (Real.log (n : Real) : Complex) * (t : Complex)) := by
      rw [LSeries.term_of_ne_zero hn, vonMangoldtComplex,
        Complex.cpow_def_of_ne_zero hncast]
      rw [← Complex.natCast_log]
      rw [div_eq_mul_inv, ← Complex.exp_neg]
      rw [show
          -((Real.log (n : Real) : Complex) *
            ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
          ((-(5 / 4 : Real) * Real.log (n : Real) : Real) : Complex) +
            (-Complex.I * (Real.log (n : Real) : Complex) * (t : Complex)) by
        apply Complex.ext <;> simp <;> ring]
      rw [Complex.exp_add]
      ring
    have hintegrand :
        guinandWeilXiRightPrimeIntegrand p n = fun t : Real =>
          ((ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp
              ((-(5 / 4 : Real) * Real.log (n : Real) : Real) : Complex)) *
          (guinandWeilPiPolynomialGaussianSource p
              ((t : Complex) - (3 / 4 : Real) * Complex.I) *
            Complex.exp
              (-Complex.I * (Real.log (n : Real) : Complex) * (t : Complex))) := by
      funext t
      rw [guinandWeilXiRightPrimeIntegrand, hterm]
      ring
    rw [hintegrand, MeasureTheory.integral_const_mul,
      integral_guinandWeilPiPolynomialGaussianSource_xiRightLine_mul_exp_eq_fourier]
    have hexpcombine :
        Complex.exp
            ((-(5 / 4 : Real) * Real.log (n : Real) : Real) : Complex) *
          Complex.exp
            (((3 / 4 : Real) * Real.log (n : Real) : Real) : Complex) =
        Complex.exp
          ((-(1 / 2 : Real) * Real.log (n : Real) : Real) : Complex) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp
              ((-(5 / 4 : Real) * Real.log (n : Real) : Real) : Complex) *
          (Complex.exp
              (((3 / 4 : Real) * Real.log (n : Real) : Real) : Complex) *
            FourierTransform.fourier
              (fun x : Real =>
                guinandWeilPiPolynomialGaussianSource p (x : Complex))
              (Real.log (n : Real) / (2 * Real.pi))) =
          (ArithmeticFunction.vonMangoldt n : Complex) *
            (Complex.exp
                ((-(5 / 4 : Real) * Real.log (n : Real) : Real) : Complex) *
              Complex.exp
                (((3 / 4 : Real) * Real.log (n : Real) : Real) : Complex)) *
            FourierTransform.fourier
              (fun x : Real =>
                guinandWeilPiPolynomialGaussianSource p (x : Complex))
              (Real.log (n : Real) / (2 * Real.pi)) := by ring
      _ = (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp
              ((-(1 / 2 : Real) * Real.log (n : Real) : Real) : Complex) *
            FourierTransform.fourier
              (fun x : Real =>
                guinandWeilPiPolynomialGaussianSource p (x : Complex))
              (Real.log (n : Real) / (2 * Real.pi)) := by
        rw [hexpcombine]

/-- The residual exponential coefficient is exactly the inverse square root. -/
theorem exp_neg_half_log_natCast_eq_inv_sqrt
    (n : Nat) (hn : n ≠ 0) :
    Complex.exp
        ((-(1 / 2 : Real) * Real.log (n : Real) : Real) : Complex) =
      ((1 / Real.sqrt (n : Real) : Real) : Complex) := by
  rw [← Complex.ofReal_exp]
  congr 1
  have hnpos : 0 < (n : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc
    Real.exp (-(1 / 2 : Real) * Real.log (n : Real)) =
        (n : Real) ^ (-(1 / 2 : Real)) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    _ = ((n : Real) ^ (1 / 2 : Real))⁻¹ :=
      Real.rpow_neg (le_of_lt hnpos) _
    _ = 1 / Real.sqrt (n : Real) := by
      simp only [Real.sqrt_eq_rpow, one_div]

/-- One right-line prime term in the literature square-root normalization. -/
theorem integral_guinandWeilXiRightPrimeIntegrand_eq_invSqrt_fourier
    (p : Polynomial Complex) (n : Nat) :
    (∫ t : Real, guinandWeilXiRightPrimeIntegrand p n t) =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) : Real) : Complex) *
        FourierTransform.fourier
          (fun x : Real =>
            guinandWeilPiPolynomialGaussianSource p (x : Complex))
          (Real.log (n : Real) / (2 * Real.pi)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [guinandWeilXiRightPrimeIntegrand]
  · rw [integral_guinandWeilXiRightPrimeIntegrand_eq_fourier,
      exp_neg_half_log_natCast_eq_inv_sqrt n hn]
    push_cast
    ring

private theorem shiftedSource_integrable (p : Polynomial Complex) :
    Integrable fun t : Real =>
      guinandWeilPiPolynomialGaussianSource p
        ((t : Complex) - (3 / 4 : Real) * Complex.I) := by
  have h :=
    integrable_guinandWeilPiPolynomialGaussianSource_horizontalLine_mul_exp
      p 0 (-(3 / 4 : Real))
  simpa only [sub_eq_add_neg, neg_mul, ofReal_neg, ofReal_zero, mul_zero,
    zero_mul, Complex.exp_zero, mul_one] using h

private theorem norm_vonMangoldt_term_rightLine
    (n : Nat) (t : Real) :
    norm (LSeries.term vonMangoldtComplex
      ((5 / 4 : Real) + (t : Complex) * Complex.I) n) =
      norm (LSeries.term vonMangoldtComplex (5 / 4 : Real) n) := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp

private theorem integrable_guinandWeilXiRightPrimeIntegrand
    (p : Polynomial Complex) (n : Nat) :
    Integrable (guinandWeilXiRightPrimeIntegrand p n) := by
  let c : Real := norm (LSeries.term vonMangoldtComplex (5 / 4 : Real) n)
  have hsource := shiftedSource_integrable p
  have hmajor : Integrable fun t : Real =>
      c * norm (guinandWeilPiPolynomialGaussianSource p
        ((t : Complex) - (3 / 4 : Real) * Complex.I)) :=
    hsource.norm.const_mul c
  refine hmajor.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hterm : Continuous fun t : Real =>
        LSeries.term vonMangoldtComplex
          ((5 / 4 : Real) + (t : Complex) * Complex.I) n := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero]
        exact continuous_const
      · simp only [LSeries.term_of_ne_zero hn]
        have hpow : Continuous fun t : Real =>
            (n : Complex) ^ ((5 / 4 : Real) + (t : Complex) * Complex.I) := by
          simp_rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
          fun_prop
        apply Continuous.div continuous_const hpow
        intro t
        exact Complex.cpow_ne_zero_iff.mpr
          (Or.inl (Nat.cast_ne_zero.mpr hn))
    have hsource : Continuous fun t : Real =>
        guinandWeilPiPolynomialGaussianSource p
          ((t : Complex) - (3 / 4 : Real) * Complex.I) :=
      (p.differentiable_aeval.mul
        differentiable_guinandWeilPiGaussianSource).continuous.comp (by fun_prop)
    exact (hsource.mul hterm).aestronglyMeasurable
  · simp only [guinandWeilXiRightPrimeIntegrand, norm_mul]
    rw [norm_vonMangoldt_term_rightLine]
    dsimp only [c]
    rw [mul_comm]

private theorem integral_norm_guinandWeilXiRightPrimeIntegrand
    (p : Polynomial Complex) (n : Nat) :
    (∫ t : Real, norm (guinandWeilXiRightPrimeIntegrand p n t)) =
      norm (LSeries.term vonMangoldtComplex (5 / 4 : Real) n) *
        ∫ t : Real,
          norm (guinandWeilPiPolynomialGaussianSource p
            ((t : Complex) - (3 / 4 : Real) * Complex.I)) := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [guinandWeilXiRightPrimeIntegrand, norm_mul,
    norm_vonMangoldt_term_rightLine]
  ring

private theorem summable_integral_norm_guinandWeilXiRightPrimeIntegrand
    (p : Polynomial Complex) :
    Summable fun n : Nat =>
      ∫ t : Real, norm (guinandWeilXiRightPrimeIntegrand p n t) := by
  have hs : LSeriesSummable vonMangoldtComplex (5 / 4 : Real) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hnorm : Summable fun n : Nat =>
      norm (LSeries.term vonMangoldtComplex (5 / 4 : Real) n) :=
    summable_norm_iff.mpr hs
  have hmul := hnorm.mul_right
    (∫ t : Real,
      norm (guinandWeilPiPolynomialGaussianSource p
        ((t : Complex) - (3 / 4 : Real) * Complex.I)))
  simpa only [integral_norm_guinandWeilXiRightPrimeIntegrand] using hmul

/--
The complete right-line integral may be interchanged with the von Mangoldt
L-series.  No finite cutoff or conditional convergence hypothesis remains.
-/
theorem integral_shiftedPolynomialGaussian_mul_vonMangoldtLSeries_eq_tsum
    (p : Polynomial Complex) :
    (∫ t : Real,
        guinandWeilPiPolynomialGaussianSource p
            ((t : Complex) - (3 / 4 : Real) * Complex.I) *
          LSeries vonMangoldtComplex
            ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
      ∑' n : Nat, ∫ t : Real, guinandWeilXiRightPrimeIntegrand p n t := by
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm
    (integrable_guinandWeilXiRightPrimeIntegrand p)
    (summable_integral_norm_guinandWeilXiRightPrimeIntegrand p)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [guinandWeilXiRightPrimeIntegrand, LSeries]
  rw [← tsum_mul_left]

/--
Complete positive-frequency prime evaluation on the xi right vertical, with
the exact `1/sqrt n` coefficient and `log n/(2*pi)` Fourier sample.
-/
theorem integral_shiftedPolynomialGaussian_mul_vonMangoldtLSeries_eq_primeFourierTsum
    (p : Polynomial Complex) :
    (∫ t : Real,
        guinandWeilPiPolynomialGaussianSource p
            ((t : Complex) - (3 / 4 : Real) * Complex.I) *
          LSeries vonMangoldtComplex
            ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
      ∑' n : Nat,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) : Real) : Complex) *
          FourierTransform.fourier
            (fun x : Real =>
              guinandWeilPiPolynomialGaussianSource p (x : Complex))
            (Real.log (n : Real) / (2 * Real.pi)) := by
  rw [integral_shiftedPolynomialGaussian_mul_vonMangoldtLSeries_eq_tsum]
  apply tsum_congr
  intro n
  exact integral_guinandWeilXiRightPrimeIntegrand_eq_invSqrt_fourier p n

private theorem summable_invSqrt_mul_fourier_polynomialGaussian
    (p : Polynomial Complex) :
    Summable fun n : Nat =>
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) : Real) : Complex) *
        FourierTransform.fourier
          (fun x : Real =>
            guinandWeilPiPolynomialGaussianSource p (x : Complex))
          (Real.log (n : Real) / (2 * Real.pi)) := by
  refine
    (summable_integral_norm_guinandWeilXiRightPrimeIntegrand p).of_norm_bounded
      (fun n => ?_)
  rw [← integral_guinandWeilXiRightPrimeIntegrand_eq_invSqrt_fourier]
  exact norm_integral_le_integral_norm _

/-- The complete weighted von Mangoldt series on `re s = 5/4` is integrable. -/
theorem integrable_shiftedPolynomialGaussian_mul_vonMangoldtLSeries
    (p : Polynomial Complex) :
    Integrable fun t : Real =>
      guinandWeilPiPolynomialGaussianSource p
          ((t : Complex) - (3 / 4 : Real) * Complex.I) *
        LSeries vonMangoldtComplex
          ((5 / 4 : Real) + (t : Complex) * Complex.I) := by
  let C : Real := ∑' n : Nat,
    norm (LSeries.term vonMangoldtComplex (5 / 4 : Real) n)
  have hsNorm : Summable fun n : Nat =>
      norm (LSeries.term vonMangoldtComplex (5 / 4 : Real) n) := by
    exact summable_norm_iff.mpr
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  have hCnonneg : 0 <= C := tsum_nonneg fun _ => norm_nonneg _
  have hmajor : Integrable fun t : Real =>
      C * norm (guinandWeilPiPolynomialGaussianSource p
        ((t : Complex) - (3 / 4 : Real) * Complex.I)) :=
    (shiftedSource_integrable p).norm.const_mul C
  refine hmajor.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hfun :
        (fun t : Real =>
          guinandWeilPiPolynomialGaussianSource p
              ((t : Complex) - (3 / 4 : Real) * Complex.I) *
            LSeries vonMangoldtComplex
              ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
          fun t : Real => ∑' n : Nat,
            guinandWeilXiRightPrimeIntegrand p n t := by
      funext t
      simp only [guinandWeilXiRightPrimeIntegrand, LSeries]
      rw [<- tsum_mul_left]
    rw [hfun]
    exact AEStronglyMeasurable.tsum fun n =>
      (integrable_guinandWeilXiRightPrimeIntegrand p n).aestronglyMeasurable
  · have hs : LSeriesSummable vonMangoldtComplex
        ((5 / 4 : Real) + (t : Complex) * Complex.I) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
    have hLSeries :
        norm (LSeries vonMangoldtComplex
          ((5 / 4 : Real) + (t : Complex) * Complex.I)) <= C := by
      rw [LSeries]
      calc
        norm (∑' n : Nat, LSeries.term vonMangoldtComplex
            ((5 / 4 : Real) + (t : Complex) * Complex.I) n) <=
            ∑' n : Nat, norm (LSeries.term vonMangoldtComplex
              ((5 / 4 : Real) + (t : Complex) * Complex.I) n) :=
          norm_tsum_le_tsum_norm (summable_norm_iff.mpr hs)
        _ = C := by
          apply tsum_congr
          intro n
          exact norm_vonMangoldt_term_rightLine n t
    simp only [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hCnonneg (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_left hLSeries (norm_nonneg _)).trans_eq
      (mul_comm _ _)

/-- The prime contribution in the actual xi right-line coordinate is integrable. -/
theorem integrable_xiContourWeight_vonMangoldtLSeries_right
    (p : Polynomial Real) :
    Integrable fun t : Real =>
      guinandWeilXiContourWeight p
          ((5 / 4 : Real) + (t : Complex) * Complex.I) *
        LSeries (fun n : Nat =>
            (ArithmeticFunction.vonMangoldt n : Complex))
          ((5 / 4 : Real) + (t : Complex) * Complex.I) := by
  let q : Polynomial Complex := guinandWeilPiEvenPolynomial p
  have h := integrable_shiftedPolynomialGaussian_mul_vonMangoldtLSeries q
  have hweight :
      (fun t : Real =>
        guinandWeilXiContourWeight p
            ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
        fun t : Real =>
          guinandWeilPiPolynomialGaussianSource q
            ((t : Complex) - (3 / 4 : Real) * Complex.I) := by
    funext t
    unfold guinandWeilXiContourWeight q
    rw [guinandWeilXiContourCoordinate_horizontal]
    norm_num
    congr 1
  apply h.congr
  filter_upwards with t
  rw [congrFun hweight t]
  rfl

/--
After reflected-line pairing, the von Mangoldt contribution on `re s = 5/4`
is exactly the literature prime side.  In particular, the minus sign from
`xi'/xi = rational + Gamma - zeta'/zeta` and both Fourier samples are present.
-/
theorem neg_one_div_pi_mul_re_integral_xiContourWeight_vonMangoldtLSeries_right_eq_literaturePrime
    (p : Polynomial Real) :
    -(1 / Real.pi) *
        (∫ t : Real,
          guinandWeilXiContourWeight p
              ((5 / 4 : Real) + (t : Complex) * Complex.I) *
            LSeries (fun n : Nat =>
                (ArithmeticFunction.vonMangoldt n : Complex))
              ((5 / 4 : Real) + (t : Complex) * Complex.I)).re =
      guinandWeilLiteraturePrimeSide
        (guinandWeilPiEvenPolynomialGaussianSchwartz p) := by
  let q : Polynomial Complex := guinandWeilPiEvenPolynomial p
  let term : Nat → Complex := fun n =>
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) : Real) : Complex) *
      FourierTransform.fourier
        (fun x : Real => guinandWeilPiPolynomialGaussianSource q (x : Complex))
        (Real.log (n : Real) / (2 * Real.pi))
  have hsum : Summable term :=
    summable_invSqrt_mul_fourier_polynomialGaussian q
  have hintegral :
      (∫ t : Real,
          guinandWeilXiContourWeight p
              ((5 / 4 : Real) + (t : Complex) * Complex.I) *
            LSeries (fun n : Nat =>
                (ArithmeticFunction.vonMangoldt n : Complex))
              ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
        ∑' n : Nat, term n := by
    have hweight (t : Real) :
        guinandWeilXiContourWeight p
            ((5 / 4 : Real) + (t : Complex) * Complex.I) =
          guinandWeilPiPolynomialGaussianSource q
            ((t : Complex) - (3 / 4 : Real) * Complex.I) := by
      unfold guinandWeilXiContourWeight q
      rw [guinandWeilXiContourCoordinate_horizontal]
      norm_num
      congr 1
    rw [MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => by
      rw [hweight])]
    change
      (∫ t : Real,
          guinandWeilPiPolynomialGaussianSource q
              ((t : Complex) - (3 / 4 : Real) * Complex.I) *
            LSeries vonMangoldtComplex
              ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
        ∑' n : Nat, term n
    simpa [term] using
      (integral_shiftedPolynomialGaussian_mul_vonMangoldtLSeries_eq_primeFourierTsum q)
  rw [hintegral, Complex.re_tsum hsum]
  rw [guinandWeilLiteraturePrimeSide, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [guinandWeilLiteraturePrimeTerm]
  have hneg :
      (SchwartzLineTestFunction.fourier
          (guinandWeilPiEvenPolynomialGaussianSchwartz p))
          (-Real.log (n : Real) / (2 * Real.pi)) =
        (SchwartzLineTestFunction.fourier
          (guinandWeilPiEvenPolynomialGaussianSchwartz p))
          (Real.log (n : Real) / (2 * Real.pi)) := by
    rw [show -Real.log (n : Real) / (2 * Real.pi) =
        -(Real.log (n : Real) / (2 * Real.pi)) by ring,
      fourier_guinandWeilPiEvenPolynomialGaussianSchwartz_neg]
  rw [hneg]
  have hsource :
      (fun x : Real => guinandWeilPiPolynomialGaussianSource q (x : Complex)) =
        fun x : Real => guinandWeilPiEvenPolynomialGaussianSchwartz p x := by
    funext x
    rfl
  simp only [term]
  rw [hsource]
  have hfourier :
      FourierTransform.fourier
          (fun x : Real => guinandWeilPiEvenPolynomialGaussianSchwartz p x)
          (Real.log (n : Real) / (2 * Real.pi)) =
        (SchwartzLineTestFunction.fourier
          (guinandWeilPiEvenPolynomialGaussianSchwartz p))
          (Real.log (n : Real) / (2 * Real.pi)) := by
    rfl
  rw [hfourier]
  simp only [q, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

end

end RiemannHypothesisProject
