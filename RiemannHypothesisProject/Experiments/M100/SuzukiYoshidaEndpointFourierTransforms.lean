import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointModes
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Fourier transforms of the endpoint Yoshida exponentials

This module begins the QF2 source-evaluation package.  It computes the
Mathlib-normalized Fourier integral of the normalized periodic exponential on
`[-r,r]`.  The resonant frequency is retained as a separate branch, so the
removable singularity is never hidden by division.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal FourierTransform

/-- The complex coefficient in the Mathlib Fourier integrand.  Mathlib uses
`exp (-2*pi*i*x*xi)`, while the endpoint mode uses
`exp (i*n*pi*x/r)`. -/
def suzukiYoshidaEndpointFourierPhase
    (r : Real) (n : Int) (xi : Real) : Complex :=
  Complex.I *
    (((n : Complex) * (Real.pi : Complex) / (r : Complex)) -
      ((2 * Real.pi * xi : Real) : Complex))

/-- The real frequency displacement underlying the complex phase. -/
def suzukiYoshidaEndpointFourierDetuning
    (r : Real) (n : Int) (xi : Real) : Real :=
  (n : Real) * Real.pi / r - 2 * Real.pi * xi

theorem suzukiYoshidaEndpointFourierPhase_eq
    (r : Real) (n : Int) (xi : Real) :
    suzukiYoshidaEndpointFourierPhase r n xi =
      Complex.I *
        (suzukiYoshidaEndpointFourierDetuning r n xi : Complex) := by
  unfold suzukiYoshidaEndpointFourierPhase
    suzukiYoshidaEndpointFourierDetuning
  norm_cast

/-- The only resonant Mathlib frequency is `n/(2r)`. -/
theorem suzukiYoshidaEndpointFourierPhase_eq_zero_iff
    {r : Real} (hr : 0 < r) (n : Int) (xi : Real) :
    suzukiYoshidaEndpointFourierPhase r n xi = 0 ↔
      xi = (n : Real) / (2 * r) := by
  unfold suzukiYoshidaEndpointFourierPhase
  rw [mul_eq_zero, or_iff_right Complex.I_ne_zero]
  norm_cast
  field_simp [hr.ne']
  constructor
  · intro h
    nlinarith [Real.pi_pos]
  · intro h
    rw [h]
    ring

/-- Endpoint exponentials are integrable, independently of their already
checked `L²` membership. -/
theorem suzukiYoshidaExponentialFunction_memLp_one
    {r : Real} (_hr : 0 < r) (n : Int) :
    MemLp (suzukiYoshidaExponentialFunction r n)
      (1 : ENNReal) (volume : Measure Real) := by
  unfold suzukiYoshidaExponentialFunction
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  haveI : IsFiniteMeasure
      ((volume : Measure Real).restrict (Set.Icc (-r) r)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_Icc_lt_top : volume (Set.Icc (-r) r) < ⊤)⟩
  refine MemLp.of_bound (C :=
    ‖((Real.sqrt (2 * r))⁻¹ : Complex)‖) (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [norm_mul, Complex.norm_exp]
    simp

/-- Fourier normalization bridge before evaluating the elementary exponential
integral. -/
theorem fourier_suzukiYoshidaExponentialFunction_eq_intervalIntegral
    {r : Real} (hr : 0 < r) (n : Int) (xi : Real) :
    𝓕 (suzukiYoshidaExponentialFunction r n) xi =
      ((Real.sqrt (2 * r))⁻¹ : Complex) *
        ∫ x in -r..r,
          Complex.exp
            (suzukiYoshidaEndpointFourierPhase r n xi * (x : Complex)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have hpoint :
      (fun x : Real =>
        Complex.exp ((-2 * Real.pi * x * xi : Real) * Complex.I) *
          suzukiYoshidaExponentialFunction r n x) =
        Set.indicator (Set.Icc (-r) r)
          (fun x : Real =>
            ((Real.sqrt (2 * r))⁻¹ : Complex) *
              Complex.exp
                (suzukiYoshidaEndpointFourierPhase r n xi *
                  (x : Complex))) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-r) r
    · simp only [suzukiYoshidaExponentialFunction,
        Set.indicator_of_mem hx]
      calc
        Complex.exp ((-2 * Real.pi * x * xi : Real) * Complex.I) *
              (((Real.sqrt (2 * r))⁻¹ : Complex) *
                Complex.exp
                  (Complex.I *
                    ((n : Complex) * (Real.pi : Complex) / (r : Complex)) *
                      (x : Complex))) =
            ((Real.sqrt (2 * r))⁻¹ : Complex) *
              (Complex.exp ((-2 * Real.pi * x * xi : Real) * Complex.I) *
                Complex.exp
                  (Complex.I *
                    ((n : Complex) * (Real.pi : Complex) / (r : Complex)) *
                      (x : Complex))) := by ring
        _ = ((Real.sqrt (2 * r))⁻¹ : Complex) *
              Complex.exp
                (((-2 * Real.pi * x * xi : Real) : Complex) * Complex.I +
                  Complex.I *
                    ((n : Complex) * (Real.pi : Complex) / (r : Complex)) *
                      (x : Complex)) := by rw [Complex.exp_add]
        _ = ((Real.sqrt (2 * r))⁻¹ : Complex) *
              Complex.exp
                (suzukiYoshidaEndpointFourierPhase r n xi *
                  (x : Complex)) := by
            congr 2
            unfold suzukiYoshidaEndpointFourierPhase
            push_cast
            ring
    · simp [suzukiYoshidaExponentialFunction, hx]
  rw [hpoint, MeasureTheory.integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  rw [intervalIntegral.integral_const_mul]

/-- Exact elementary evaluation of the endpoint exponential integral.  The
zero-phase branch is the removable singularity. -/
theorem integral_suzukiYoshidaEndpointFourierPhase
    {r : Real} (_hr : 0 < r) (n : Int) (xi : Real) :
    (∫ x in -r..r,
        Complex.exp
          (suzukiYoshidaEndpointFourierPhase r n xi * (x : Complex))) =
      if suzukiYoshidaEndpointFourierPhase r n xi = 0 then
        ((2 * r : Real) : Complex)
      else
        (Complex.exp (suzukiYoshidaEndpointFourierPhase r n xi * r) -
            Complex.exp
              (suzukiYoshidaEndpointFourierPhase r n xi * (-r))) /
          suzukiYoshidaEndpointFourierPhase r n xi := by
  by_cases hphase : suzukiYoshidaEndpointFourierPhase r n xi = 0
  · rw [if_pos hphase]
    simp [hphase]
    ring
  · rw [if_neg hphase]
    simpa only [Complex.ofReal_neg] using
      (integral_exp_mul_complex (a := -r) (b := r) hphase)

/-- Exact Mathlib-normalized Fourier transform of the endpoint exponential,
including the resonant branch. -/
theorem fourier_suzukiYoshidaExponentialFunction
    {r : Real} (hr : 0 < r) (n : Int) (xi : Real) :
    𝓕 (suzukiYoshidaExponentialFunction r n) xi =
      ((Real.sqrt (2 * r))⁻¹ : Complex) *
        if suzukiYoshidaEndpointFourierPhase r n xi = 0 then
          ((2 * r : Real) : Complex)
        else
          (Complex.exp (suzukiYoshidaEndpointFourierPhase r n xi * r) -
              Complex.exp
                (suzukiYoshidaEndpointFourierPhase r n xi * (-r))) /
            suzukiYoshidaEndpointFourierPhase r n xi := by
  rw [fourier_suzukiYoshidaExponentialFunction_eq_intervalIntegral hr,
    integral_suzukiYoshidaEndpointFourierPhase hr]

/-- At the removable singularity, the transform has the normalized interval
mass `sqrt (2r)`. -/
theorem fourier_suzukiYoshidaExponentialFunction_resonant
    {r : Real} (hr : 0 < r) (n : Int) :
    𝓕 (suzukiYoshidaExponentialFunction r n)
        ((n : Real) / (2 * r)) =
      (Real.sqrt (2 * r) : Complex) := by
  rw [fourier_suzukiYoshidaExponentialFunction hr]
  rw [if_pos ((suzukiYoshidaEndpointFourierPhase_eq_zero_iff
    hr n ((n : Real) / (2 * r))).2 rfl)]
  have hsqrt : Real.sqrt (2 * r) ≠ 0 := by positivity
  norm_cast
  have hsquare : Real.sqrt (2 * r) ^ 2 = 2 * r :=
    Real.sq_sqrt (by positivity)
  calc
    (Real.sqrt (2 * r))⁻¹ * (2 * r) =
        (Real.sqrt (2 * r))⁻¹ * Real.sqrt (2 * r) ^ 2 := by rw [hsquare]
    _ = Real.sqrt (2 * r) := by field_simp [hsqrt]

/-- Away from resonance, the elementary complex quotient is the real sine
quotient expected from Suzuki's endpoint transform. -/
theorem suzukiYoshidaEndpointFourierPhase_quotient_eq_sine
    {r : Real} (n : Int) (xi : Real)
    (hphase : suzukiYoshidaEndpointFourierPhase r n xi ≠ 0) :
    (Complex.exp (suzukiYoshidaEndpointFourierPhase r n xi * r) -
          Complex.exp
            (suzukiYoshidaEndpointFourierPhase r n xi * (-r))) /
        suzukiYoshidaEndpointFourierPhase r n xi =
      ((2 * Real.sin
          (suzukiYoshidaEndpointFourierDetuning r n xi * r) /
        suzukiYoshidaEndpointFourierDetuning r n xi : Real) : Complex) := by
  let d := suzukiYoshidaEndpointFourierDetuning r n xi
  have hphaseEq :
      suzukiYoshidaEndpointFourierPhase r n xi =
        Complex.I * (d : Complex) := by
    exact suzukiYoshidaEndpointFourierPhase_eq r n xi
  have hd : d ≠ 0 := by
    intro hd
    apply hphase
    rw [hphaseEq, hd]
    norm_num
  rw [hphaseEq]
  change
    (Complex.exp (Complex.I * (d : Complex) * (r : Complex)) -
          Complex.exp (Complex.I * (d : Complex) * (-(r : Complex)))) /
        (Complex.I * (d : Complex)) =
      ((2 * Real.sin (d * r) / d : Real) : Complex)
  have hpos :
      Complex.I * (d : Complex) * (r : Complex) =
        ((d * r : Real) : Complex) * Complex.I := by
    push_cast
    ring
  have hneg :
      Complex.I * (d : Complex) * (-(r : Complex)) =
        ((-(d * r) : Real) : Complex) * Complex.I := by
    push_cast
    ring
  rw [hpos, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  norm_cast
  field_simp [hd, Complex.I_ne_zero]
  push_cast
  ring

/-- Nonresonant source-facing sine-quotient form of the normalized endpoint
Fourier transform. -/
theorem fourier_suzukiYoshidaExponentialFunction_nonresonant
    {r : Real} (hr : 0 < r) (n : Int) (xi : Real)
    (hxi : xi ≠ (n : Real) / (2 * r)) :
    𝓕 (suzukiYoshidaExponentialFunction r n) xi =
      ((Real.sqrt (2 * r))⁻¹ : Complex) *
        ((2 * Real.sin
            (suzukiYoshidaEndpointFourierDetuning r n xi * r) /
          suzukiYoshidaEndpointFourierDetuning r n xi : Real) : Complex) := by
  have hphase : suzukiYoshidaEndpointFourierPhase r n xi ≠ 0 :=
    mt (suzukiYoshidaEndpointFourierPhase_eq_zero_iff hr n xi).mp hxi
  rw [fourier_suzukiYoshidaExponentialFunction hr, if_neg hphase,
    suzukiYoshidaEndpointFourierPhase_quotient_eq_sine n xi hphase]

/-- Away from resonance, the normalized endpoint transform is bounded by the
reciprocal of its real frequency detuning.  This is the sharp decay estimate
needed for the logarithmically weighted tail. -/
theorem norm_fourier_suzukiYoshidaExponentialFunction_le_detuning
    {r : Real} (hr : 0 < r) (n : Int) (xi : Real)
    (hphase : suzukiYoshidaEndpointFourierPhase r n xi ≠ 0) :
    ‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi‖ ≤
      2 / (Real.sqrt (2 * r) *
        |suzukiYoshidaEndpointFourierDetuning r n xi|) := by
  rw [fourier_suzukiYoshidaExponentialFunction hr, if_neg hphase]
  have hsqrt : 0 < Real.sqrt (2 * r) := by positivity
  have hdetuning : suzukiYoshidaEndpointFourierDetuning r n xi ≠ 0 := by
    intro hzero
    apply hphase
    rw [suzukiYoshidaEndpointFourierPhase_eq, hzero]
    norm_num
  have hnumerator :
      ‖Complex.exp (suzukiYoshidaEndpointFourierPhase r n xi * r) -
          Complex.exp
            (suzukiYoshidaEndpointFourierPhase r n xi * (-r))‖ ≤ 2 := by
    calc
      _ ≤
          ‖Complex.exp (suzukiYoshidaEndpointFourierPhase r n xi * r)‖ +
            ‖Complex.exp
              (suzukiYoshidaEndpointFourierPhase r n xi * (-r))‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp, Complex.norm_exp]
        rw [suzukiYoshidaEndpointFourierPhase_eq,
          Complex.mul_re, Complex.mul_re]
        norm_num
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsqrt, norm_div]
  have hphaseNorm :
      ‖suzukiYoshidaEndpointFourierPhase r n xi‖ =
        |suzukiYoshidaEndpointFourierDetuning r n xi| := by
    rw [suzukiYoshidaEndpointFourierPhase_eq, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hphaseNorm]
  have hrewrite :
      (Real.sqrt (2 * r))⁻¹ *
          (‖Complex.exp (suzukiYoshidaEndpointFourierPhase r n xi * r) -
              Complex.exp
                (suzukiYoshidaEndpointFourierPhase r n xi * (-r))‖ /
            |suzukiYoshidaEndpointFourierDetuning r n xi|) =
        ‖Complex.exp (suzukiYoshidaEndpointFourierPhase r n xi * r) -
              Complex.exp
                (suzukiYoshidaEndpointFourierPhase r n xi * (-r))‖ /
          (Real.sqrt (2 * r) *
            |suzukiYoshidaEndpointFourierDetuning r n xi|) := by
    field_simp [hsqrt.ne', hdetuning]
  rw [hrewrite]
  exact div_le_div_of_nonneg_right hnumerator (by positivity)

/-- Once `|xi|` dominates the mode frequency, the detuning is at least
`pi * |xi|`.  This packages the reverse-triangle estimate used in the QF2
high-frequency majorant. -/
theorem pi_mul_abs_le_abs_suzukiYoshidaEndpointFourierDetuning
    {r : Real} (hr : 0 < r) (n : Int) (xi : Real)
    (hxi : |(n : Real)| / r ≤ |xi|) :
    Real.pi * |xi| ≤
      |suzukiYoshidaEndpointFourierDetuning r n xi| := by
  have hreverse :
      |2 * xi| - |(n : Real) / r| ≤
        |2 * xi - (n : Real) / r| :=
    abs_sub_abs_le_abs_sub _ _
  have hmode : |(n : Real) / r| = |(n : Real)| / r := by
    rw [abs_div, abs_of_pos hr]
  have htwo : |2 * xi| = 2 * |xi| := by
    rw [abs_mul]
    norm_num
  have hbase : |xi| ≤ |(n : Real) / r - 2 * xi| := by
    rw [abs_sub_comm]
    rw [hmode, htwo] at hreverse
    linarith
  have hdetuning :
      suzukiYoshidaEndpointFourierDetuning r n xi =
        Real.pi * ((n : Real) / r - 2 * xi) := by
    unfold suzukiYoshidaEndpointFourierDetuning
    ring
  rw [hdetuning, abs_mul, abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left hbase Real.pi_pos.le

/-- Concrete high-frequency `1 / |xi|` decay for every endpoint mode.  The
threshold keeps the removable singularity outside the tail and is convenient
for later compact/tail decomposition. -/
theorem norm_fourier_suzukiYoshidaExponentialFunction_le_highFrequency
    {r : Real} (hr : 0 < r) (n : Int) (xi : Real)
    (hxi : max 1 (|(n : Real)| / r) ≤ |xi|) :
    ‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi‖ ≤
      2 / (Real.sqrt (2 * r) * Real.pi * |xi|) := by
  have hxiMode : |(n : Real)| / r ≤ |xi| :=
    (le_max_right _ _).trans hxi
  have hxiPos : 0 < |xi| :=
    zero_lt_one.trans_le ((le_max_left _ _).trans hxi)
  have hdetuning :=
    pi_mul_abs_le_abs_suzukiYoshidaEndpointFourierDetuning hr n xi hxiMode
  have hdetuningPos :
      0 < |suzukiYoshidaEndpointFourierDetuning r n xi| :=
    (mul_pos Real.pi_pos hxiPos).trans_le hdetuning
  have hphase : suzukiYoshidaEndpointFourierPhase r n xi ≠ 0 := by
    rw [suzukiYoshidaEndpointFourierPhase_eq]
    apply mul_ne_zero Complex.I_ne_zero
    exact_mod_cast (abs_pos.mp hdetuningPos)
  refine (norm_fourier_suzukiYoshidaExponentialFunction_le_detuning
    hr n xi hphase).trans ?_
  apply div_le_div_of_nonneg_left (by norm_num : (0 : Real) ≤ 2)
  · positivity
  · have hsqrt : 0 < Real.sqrt (2 * r) := by positivity
    calc
      Real.sqrt (2 * r) * Real.pi * |xi| =
          Real.sqrt (2 * r) * (Real.pi * |xi|) := by ring
      _ ≤ Real.sqrt (2 * r) *
          |suzukiYoshidaEndpointFourierDetuning r n xi| :=
        mul_le_mul_of_nonneg_left hdetuning hsqrt.le

/-- Source-normalized form of the endpoint transform.  Substitution
`xi = -z/(2*pi)` converts Mathlib's convention into Suzuki's
`2*sin(r*z+n*pi)/(z+n*pi/r)` formula, including the endpoint normalization. -/
theorem fourier_suzukiYoshidaExponentialFunction_eq_sourceFormula
    {r : Real} (hr : 0 < r) (n : Int) (z : Real)
    (hz : z ≠ -((n : Real) * Real.pi / r)) :
    𝓕 (suzukiYoshidaExponentialFunction r n)
        (-z / (2 * Real.pi)) =
      ((Real.sqrt (2 * r))⁻¹ : Complex) *
        ((2 * Real.sin (r * z + (n : Real) * Real.pi) /
          (z + (n : Real) * Real.pi / r) : Real) : Complex) := by
  have hxi :
      -z / (2 * Real.pi) ≠ (n : Real) / (2 * r) := by
    intro h
    apply hz
    field_simp [Real.pi_ne_zero, hr.ne'] at h ⊢
    nlinarith
  rw [fourier_suzukiYoshidaExponentialFunction_nonresonant hr n _ hxi]
  have hdetuning :
      suzukiYoshidaEndpointFourierDetuning r n
          (-z / (2 * Real.pi)) =
        z + (n : Real) * Real.pi / r := by
    unfold suzukiYoshidaEndpointFourierDetuning
    field_simp [Real.pi_ne_zero, hr.ne']
    ring
  rw [hdetuning]
  congr 3
  field_simp [hr.ne']

end

end RiemannHypothesisProject.Experiments.M100
