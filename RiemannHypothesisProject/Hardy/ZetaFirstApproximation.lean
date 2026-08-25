import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.ZetaValues

/-!
# Hardy's zeta first approximation: source estimates

This file directly formalises the Titchmarsh Theorem 4.11 specialisation used
in Hardy's theorem for the fixed source choice `C₀ = 2`, `x(T) = 3 * T / π`.
It includes the cutoff and nonresonance estimates, the source Fourier-mode
integration-by-parts identity through the improper-tail limit, and the
pole-correction estimate.

The Fourier reconstruction is identified with the source sawtooth Euler
remainder, analytic continuation inserts that remainder into the zeta
Euler-summation identity on the positive critical line, and finite Abel
summation transports it to the exact floored cutoff.  The terminal theorem
gives the uniform `K / sqrt T` first approximation on each dyadic interval.
-/

open scoped ComplexConjugate

open Complex Filter MeasureTheory Set Topology

namespace RiemannHypothesisProject

namespace Hardy

noncomputable section

/-- The exact natural cutoff corresponding to `n ≤ 3T/π`. -/
def zetaFirstApproximationCutoff (T : Real) : Nat :=
  ⌊3 * T / Real.pi⌋₊

/--
The floored cutoff retains strict slack in Titchmarsh's source condition.

With source constant `C₀ = 2`, the required upper height is
`2 * π * N / C₀ = π * N`.  Taking `T ≥ 4` absorbs the loss of less than one
caused by flooring `3T/π`.
-/
theorem zetaFirstApproximationCutoff_sourceCondition
    {T t : Real} (hT : 4 ≤ T) (ht : T ≤ t) (ht' : t ≤ 2 * T) :
    |t| < Real.pi * (zetaFirstApproximationCutoff T : Real) := by
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have ht_nonneg : 0 ≤ t := hT_pos.le.trans ht
  have hx_nonneg : 0 ≤ 3 * T / Real.pi := by positivity
  have hfloor :
      3 * T / Real.pi < (zetaFirstApproximationCutoff T : Real) + 1 := by
    simpa [zetaFirstApproximationCutoff] using
      (Nat.lt_floor_add_one (3 * T / Real.pi))
  have hscaled : 3 * T < Real.pi * ((zetaFirstApproximationCutoff T : Real) + 1) := by
    simpa [mul_comm] using (div_lt_iff₀ Real.pi_pos).mp hfloor
  have hpi_lt_T : Real.pi < T :=
    (Real.pi_lt_four.trans_le hT)
  rw [abs_of_nonneg ht_nonneg]
  nlinarith [Real.pi_pos]

/-- The integer immediately after the exact cutoff lies strictly beyond the source tail start. -/
theorem zetaFirstApproximationCutoff_lt_succ
    {T : Real} (_hT : 0 < T) :
    3 * T / Real.pi < (zetaFirstApproximationCutoff T : Real) + 1 := by
  simpa [zetaFirstApproximationCutoff] using
    (Nat.lt_floor_add_one (3 * T / Real.pi))

/-- The integer tail start loses less than one relative to the real source cutoff. -/
theorem zetaFirstApproximationCutoff_succ_le
    {T : Real} (hT : 0 < T) :
    (zetaFirstApproximationCutoff T : Real) + 1 ≤ 3 * T / Real.pi + 1 := by
  have hx_nonneg : 0 ≤ 3 * T / Real.pi := by positivity
  have hfloor : (zetaFirstApproximationCutoff T : Real) ≤ 3 * T / Real.pi := by
    simpa [zetaFirstApproximationCutoff] using Nat.floor_le hx_nonneg
  linarith

/-- The logarithmic phase used in the source sum-to-integral comparison. -/
def zetaFirstApproximationPhase (t u : Real) : Real :=
  t * Real.log u / (2 * Real.pi)

/-- The source phase derivative as a `HasDerivAt` statement. -/
theorem hasDerivAt_zetaFirstApproximationPhase
    {t u : Real} (hu : 0 < u) :
    HasDerivAt (zetaFirstApproximationPhase t)
      (t / (2 * Real.pi * u)) u := by
  have hlog := Real.hasDerivAt_log hu.ne'
  have hderiv := (hlog.const_mul t).div_const (2 * Real.pi)
  change HasDerivAt (fun v : Real => t * Real.log v / (2 * Real.pi))
    (t / (2 * Real.pi * u)) u
  exact hderiv.congr_deriv (by
    field_simp [Real.pi_ne_zero, hu.ne'])

/-- The source phase has the expected derivative on the positive half-line. -/
theorem deriv_zetaFirstApproximationPhase
    {t u : Real} (hu : 0 < u) :
    deriv (zetaFirstApproximationPhase t) u =
      t / (2 * Real.pi * u) := by
  exact (hasDerivAt_zetaFirstApproximationPhase hu).deriv

/-- The real phase of the `n`th Fourier mode in the source tail. -/
def zetaFirstApproximationModePhase (t : Real) (n : Int) (u : Real) : Real :=
  2 * Real.pi * ((n : Real) * u - zetaFirstApproximationPhase t u)

/-- The slope of the `n`th Fourier-mode phase. -/
def zetaFirstApproximationModeSlope (t : Real) (n : Int) (u : Real) : Real :=
  2 * Real.pi * ((n : Real) - t / (2 * Real.pi * u))

/-- The source Fourier-mode phase has the explicit nonstationary slope. -/
theorem hasDerivAt_zetaFirstApproximationModePhase
    {t u : Real} (n : Int) (hu : 0 < u) :
    HasDerivAt (zetaFirstApproximationModePhase t n)
      (zetaFirstApproximationModeSlope t n u) u := by
  have hlinear : HasDerivAt (fun v : Real => (n : Real) * v) (n : Real) u :=
    by simpa only [id_eq, mul_one] using
      (hasDerivAt_id u).const_mul (n : Real)
  have hphase := hasDerivAt_zetaFirstApproximationPhase (t := t) hu
  have hderiv := (hlinear.sub hphase).const_mul (2 * Real.pi)
  change HasDerivAt
    (fun v : Real => 2 * Real.pi *
      ((n : Real) * v - zetaFirstApproximationPhase t v))
    (2 * Real.pi * ((n : Real) - t / (2 * Real.pi * u))) u
  exact hderiv

/-- The derivative form of the explicit Fourier-mode slope identity. -/
theorem deriv_zetaFirstApproximationModePhase
    {t u : Real} (n : Int) (hu : 0 < u) :
    deriv (zetaFirstApproximationModePhase t n) u =
      zetaFirstApproximationModeSlope t n u := by
  exact (hasDerivAt_zetaFirstApproximationModePhase n hu).deriv

/-- The Fourier-mode slope varies at the explicit rate `t / u²`. -/
theorem hasDerivAt_zetaFirstApproximationModeSlope
    {t u : Real} (n : Int) (hu : 0 < u) :
    HasDerivAt (zetaFirstApproximationModeSlope t n) (t / u ^ 2) u := by
  have hden : HasDerivAt (fun v : Real => 2 * Real.pi * v)
      (2 * Real.pi) u := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id u).const_mul (2 * Real.pi)
  have hden_ne : 2 * Real.pi * u ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hu.ne'
  have hquot := (hasDerivAt_const u t).div hden hden_ne
  have hinner := (hasDerivAt_const u (n : Real)).sub hquot
  have hslope := hinner.const_mul (2 * Real.pi)
  change HasDerivAt
    (fun v : Real => 2 * Real.pi *
      ((n : Real) - t / (2 * Real.pi * v))) (t / u ^ 2) u
  exact hslope.congr_deriv (by
    field_simp [Real.pi_ne_zero, hu.ne']
    ring)

/-- The unit-modulus complex exponential carrying the `n`th source mode. -/
def zetaFirstApproximationModeOscillation
    (t : Real) (n : Int) (u : Real) : Complex :=
  Complex.exp (Complex.I * (zetaFirstApproximationModePhase t n u : Complex))

/--
The source-specific integration-by-parts primitive: oscillation divided by
its logarithmic derivative.
-/
def zetaFirstApproximationModePrimitive
    (t : Real) (n : Int) (u : Real) : Complex :=
  zetaFirstApproximationModeOscillation t n u /
    (Complex.I * (zetaFirstApproximationModeSlope t n u : Complex))

/-- The curvature correction in the derivative of the mode primitive. -/
def zetaFirstApproximationModeCurvature
    (t : Real) (n : Int) (u : Real) : Complex :=
  zetaFirstApproximationModeOscillation t n u *
      (Complex.I * ((t / u ^ 2 : Real) : Complex)) /
    (Complex.I * (zetaFirstApproximationModeSlope t n u : Complex)) ^ 2

/-- The `u⁻³ᐟ²` amplitude occurring after the source tail normalization. -/
def zetaFirstApproximationTailAmplitude (u : Real) : Real :=
  u ^ (-3 / 2 : Real)

/-- The nonperiodic logarithmic twist in the normalized source tail. -/
def zetaFirstApproximationTailTwist (t u : Real) : Complex :=
  Complex.exp (-Complex.I * (t * Real.log u : Real))

/-- The source mode splits into its integral Fourier monomial and logarithmic twist. -/
theorem zetaFirstApproximationModeOscillation_eq_fourier_mul_tailTwist
    (t : Real) (n : Int) (u : Real) :
    zetaFirstApproximationModeOscillation t n u =
      fourier n (u : UnitAddCircle) *
        zetaFirstApproximationTailTwist t u := by
  rw [zetaFirstApproximationModeOscillation,
    zetaFirstApproximationModePhase, zetaFirstApproximationPhase,
    fourier_coe_apply, zetaFirstApproximationTailTwist]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/-- The logarithmic twist has unit modulus. -/
@[simp] theorem norm_zetaFirstApproximationTailTwist (t u : Real) :
    ‖zetaFirstApproximationTailTwist t u‖ = 1 := by
  rw [zetaFirstApproximationTailTwist, Complex.norm_exp]
  simp

/-- On the positive half-line, the normalized source weight is the critical-line complex power. -/
theorem zetaFirstApproximationTailWeight_eq_cpow
    (t : Real) {u : Real} (hu : 0 < u) :
    (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationTailTwist t u =
      (u : Complex) ^
        (-(((1 / 2 : Real) : Complex) + t * Complex.I) - 1) := by
  have huC : (u : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [show -(((1 / 2 : Real) : Complex) + t * Complex.I) - 1 =
      ((-3 / 2 : Real) : Complex) + (-t * Complex.I) by
    push_cast
    ring]
  rw [Complex.cpow_add _ _ huC, ← Complex.ofReal_cpow hu.le]
  change ((u ^ (-3 / 2 : Real) : Real) : Complex) *
      zetaFirstApproximationTailTwist t u =
    ((u ^ (-3 / 2 : Real) : Real) : Complex) *
      (u : Complex) ^ (-t * Complex.I)
  congr 1
  rw [zetaFirstApproximationTailTwist,
    Complex.cpow_def_of_ne_zero huC, ← Complex.ofReal_log hu.le]
  congr 1
  push_cast
  ring

/-- The half-endpoint correction at an integer Euler cutoff has its exact critical-line norm. -/
theorem norm_zetaFirstApproximation_integerBoundaryCorrection
    (t : Real) {a : Real} (ha : 0 < a) :
    ‖((1 / 2 : Real) : Complex) *
        (a : Complex) ^
          (-(((1 / 2 : Real) : Complex) + t * Complex.I))‖ =
      1 / (2 * Real.sqrt a) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num),
    Complex.norm_cpow_eq_rpow_re_of_pos ha]
  norm_num
  rw [Real.rpow_neg (le_of_lt ha), ← Real.sqrt_eq_rpow]
  ring

/-- The exact cutoff's integer endpoint correction is absorbed by the final `T⁻¹ᐟ²` error. -/
theorem norm_zetaFirstApproximation_cutoffBoundaryCorrection_le
    {T t : Real} (hT : 0 < T) :
    ‖((1 / 2 : Real) : Complex) *
        (((zetaFirstApproximationCutoff T : Real) + 1 : Real) : Complex) ^
          (-(((1 / 2 : Real) : Complex) + t * Complex.I))‖ ≤
      1 / Real.sqrt T := by
  let a : Real := (zetaFirstApproximationCutoff T : Real) + 1
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have hx_lt_a : 3 * T / Real.pi < a := by
    simpa [a] using zetaFirstApproximationCutoff_lt_succ hT
  have hquarter_lt_x : T / 4 < 3 * T / Real.pi := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : Real) < 4) Real.pi_pos]
    nlinarith [Real.pi_lt_four]
  have hTa : T ≤ 4 * a := by nlinarith
  have hsqrt : Real.sqrt T ≤ 2 * Real.sqrt a := by
    calc
      Real.sqrt T ≤ Real.sqrt (4 * a) := Real.sqrt_le_sqrt hTa
      _ = 2 * Real.sqrt a := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
        rw [show Real.sqrt (4 : Real) = 2 by
          convert Real.sqrt_sq_eq_abs (2 : Real) using 1 <;> norm_num]
  rw [show ((zetaFirstApproximationCutoff T : Real) + 1 : Real) = a by rfl,
    norm_zetaFirstApproximation_integerBoundaryCorrection t ha_pos]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hT) hsqrt

/-- The logarithmic tail twist is measurable. -/
theorem measurable_zetaFirstApproximationTailTwist (t : Real) :
    Measurable (zetaFirstApproximationTailTwist t) := by
  exact Complex.continuous_exp.measurable.comp
    (measurable_const.mul
      (Complex.continuous_ofReal.measurable.comp
        (measurable_const.mul Real.measurable_log)))

/-- Exact derivative of the normalized source-tail amplitude. -/
theorem hasDerivAt_zetaFirstApproximationTailAmplitude
    {u : Real} (hu : 0 < u) :
    HasDerivAt zetaFirstApproximationTailAmplitude
      ((-3 / 2 : Real) * u ^ (-5 / 2 : Real)) u := by
  change HasDerivAt (fun v : Real => v ^ (-3 / 2 : Real))
    ((-3 / 2 : Real) * u ^ (-5 / 2 : Real)) u
  convert Real.hasDerivAt_rpow_const
    (p := (-3 / 2 : Real)) (Or.inl hu.ne') using 1
  norm_num

/-- The exact derivative of the source-mode oscillatory exponential. -/
theorem hasDerivAt_zetaFirstApproximationModeOscillation
    {t u : Real} (n : Int) (hu : 0 < u) :
    HasDerivAt (zetaFirstApproximationModeOscillation t n)
      (zetaFirstApproximationModeOscillation t n u *
        (Complex.I * (zetaFirstApproximationModeSlope t n u : Complex))) u := by
  have hphase :=
    (hasDerivAt_zetaFirstApproximationModePhase (t := t) n hu).ofReal_comp
  have harg := hphase.const_mul Complex.I
  have hexp :=
    (Complex.hasDerivAt_exp
      (Complex.I * (zetaFirstApproximationModePhase t n u : Complex))).comp u harg
  change HasDerivAt
    (fun v : Real => Complex.exp
      (Complex.I * (zetaFirstApproximationModePhase t n v : Complex)))
    (Complex.exp
        (Complex.I * (zetaFirstApproximationModePhase t n u : Complex)) *
      (Complex.I * (zetaFirstApproximationModeSlope t n u : Complex))) u
  exact hexp

/-- Every source-mode oscillatory exponential has norm one. -/
@[simp] theorem norm_zetaFirstApproximationModeOscillation
    (t : Real) (n : Int) (u : Real) :
    ‖zetaFirstApproximationModeOscillation t n u‖ = 1 := by
  simp [zetaFirstApproximationModeOscillation]

/--
On the fixed Hardy cutoff, the logarithmic phase derivative stays a uniform
distance from the first nonzero Fourier frequency.  The explicit `1/3`
margin is stronger than the strict `< 1` hypothesis used in Titchmarsh's
Lemma 4.8.
-/
theorem abs_deriv_zetaFirstApproximationPhase_le_one_third
    {T t u : Real} (hT : 0 < T) (ht : 0 ≤ t) (ht' : t ≤ 2 * T)
    (hu : 3 * T / Real.pi ≤ u) :
    |deriv (zetaFirstApproximationPhase t) u| ≤ 1 / 3 := by
  have hu_pos : 0 < u := (by positivity : 0 < 3 * T / Real.pi).trans_le hu
  rw [deriv_zetaFirstApproximationPhase hu_pos,
    abs_of_nonneg (div_nonneg ht (by positivity))]
  have hscaled : 3 * T ≤ Real.pi * u := by
    have := mul_le_mul_of_nonneg_left hu Real.pi_pos.le
    field_simp [Real.pi_ne_zero] at this
    nlinarith
  rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi * u)]
  nlinarith

/--
Every nonzero Fourier mode stays uniformly away from the logarithmic phase
derivative.  The lower bound retains the mode size, so the later
integration-by-parts estimates gain a summable second inverse power after
multiplication by the sawtooth coefficient.
-/
theorem two_thirds_mul_abs_int_le_abs_int_sub_phaseDeriv
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    (2 / 3 : Real) * |(n : Real)| ≤
      |(n : Real) - deriv (zetaFirstApproximationPhase t) u| := by
  have hphase :=
    abs_deriv_zetaFirstApproximationPhase_le_one_third hT ht ht' hu
  have hn_abs : 1 ≤ |(n : Real)| := by
    exact_mod_cast (Int.one_le_abs hn)
  have htriangle :
      |(n : Real)| ≤
        |(n : Real) - deriv (zetaFirstApproximationPhase t) u| +
          |deriv (zetaFirstApproximationPhase t) u| := by
    calc
      |(n : Real)| =
          |((n : Real) - deriv (zetaFirstApproximationPhase t) u) +
            deriv (zetaFirstApproximationPhase t) u| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  nlinarith

/--
The actual derivative of the `n`th oscillatory phase is separated from zero
by a constant multiple of `|n|` throughout the Hardy tail.
Result is stated in the normalization used by the forthcoming
integration-by-parts primitive.
-/
theorem four_pi_over_three_mul_abs_int_le_abs_modeSlope
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    (4 * Real.pi / 3) * |(n : Real)| ≤
      |zetaFirstApproximationModeSlope t n u| := by
  have hu_pos : 0 < u := (by positivity : 0 < 3 * T / Real.pi).trans_le hu
  have hsep :=
    two_thirds_mul_abs_int_le_abs_int_sub_phaseDeriv n hn hT ht ht' hu
  rw [zetaFirstApproximationModeSlope,
    ← deriv_zetaFirstApproximationPhase (t := t) hu_pos, abs_mul,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  calc
    (4 * Real.pi / 3) * |(n : Real)| =
        (2 * Real.pi) * ((2 / 3 : Real) * |(n : Real)|) := by ring
    _ ≤ (2 * Real.pi) *
        |(n : Real) - deriv (zetaFirstApproximationPhase t) u| :=
      mul_le_mul_of_nonneg_left hsep (by positivity)

/-- No nonzero Fourier mode has a stationary point on the Hardy tail. -/
theorem zetaFirstApproximationModeSlope_ne_zero
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    zetaFirstApproximationModeSlope t n u ≠ 0 := by
  have hn_abs : 0 < |(n : Real)| := by
    rw [abs_pos]
    exact_mod_cast hn
  have hsep :=
    four_pi_over_three_mul_abs_int_le_abs_modeSlope n hn hT ht ht' hu
  have hpositive : 0 < |zetaFirstApproximationModeSlope t n u| :=
    (mul_pos (by positivity : 0 < 4 * Real.pi / 3) hn_abs).trans_le hsep
  exact (abs_pos.mp hpositive)

/--
Exact derivative identity for the source-specific oscillatory primitive.
The second term is the curvature correction retained by integration by parts.
-/
theorem hasDerivAt_zetaFirstApproximationModePrimitive
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    HasDerivAt (zetaFirstApproximationModePrimitive t n)
      (zetaFirstApproximationModeOscillation t n u -
        zetaFirstApproximationModeCurvature t n u) u := by
  have hu_pos : 0 < u := (by positivity : 0 < 3 * T / Real.pi).trans_le hu
  have hslope_ne :=
    zetaFirstApproximationModeSlope_ne_zero n hn hT ht ht' hu
  have hslopeC_ne :
      (zetaFirstApproximationModeSlope t n u : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hslope_ne
  have hden_ne :
      Complex.I * (zetaFirstApproximationModeSlope t n u : Complex) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hslopeC_ne
  have hnum :=
    hasDerivAt_zetaFirstApproximationModeOscillation (t := t) n hu_pos
  have hslope :=
    (hasDerivAt_zetaFirstApproximationModeSlope (t := t) n hu_pos).ofReal_comp
  have hden := hslope.const_mul Complex.I
  have hquot := hnum.div hden hden_ne
  change HasDerivAt
    (fun v : Real => zetaFirstApproximationModeOscillation t n v /
      (Complex.I * (zetaFirstApproximationModeSlope t n v : Complex))) _ u
  change HasDerivAt _
    (zetaFirstApproximationModeOscillation t n u -
      zetaFirstApproximationModeOscillation t n u *
        (Complex.I * ((t / u ^ 2 : Real) : Complex)) /
          (Complex.I *
            (zetaFirstApproximationModeSlope t n u : Complex)) ^ 2) u
  exact hquot.congr_deriv (by
    field_simp [hden_ne, hslopeC_ne])

/-- The primitive norm is exactly the reciprocal phase-slope size. -/
theorem norm_zetaFirstApproximationModePrimitive
    (t : Real) (n : Int) (u : Real) :
    ‖zetaFirstApproximationModePrimitive t n u‖ =
      1 / |zetaFirstApproximationModeSlope t n u| := by
  simp [zetaFirstApproximationModePrimitive]

/--
The oscillatory primitive gains one inverse power of the nonzero mode,
uniformly over the full Hardy tail.
-/
theorem norm_zetaFirstApproximationModePrimitive_le
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    ‖zetaFirstApproximationModePrimitive t n u‖ ≤
      1 / ((4 * Real.pi / 3) * |(n : Real)|) := by
  rw [norm_zetaFirstApproximationModePrimitive]
  have hn_abs : 0 < |(n : Real)| := by
    rw [abs_pos]
    exact_mod_cast hn
  have hden_pos : 0 < (4 * Real.pi / 3) * |(n : Real)| :=
    mul_pos (by positivity) hn_abs
  exact one_div_le_one_div_of_le hden_pos
    (four_pi_over_three_mul_abs_int_le_abs_modeSlope n hn hT ht ht' hu)

/--
The curvature term in the primitive derivative gains two inverse powers of
the Fourier mode.  This is the summable modewise contribution after the
sawtooth coefficient is inserted.
-/
theorem norm_zetaFirstApproximationModeCurvature_le
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    ‖zetaFirstApproximationModeCurvature t n u‖ ≤
      (t / u ^ 2) /
        ((4 * Real.pi / 3) * |(n : Real)|) ^ 2 := by
  have hn_abs : 0 < |(n : Real)| := by
    rw [abs_pos]
    exact_mod_cast hn
  have hbase_pos : 0 < (4 * Real.pi / 3) * |(n : Real)| :=
    mul_pos (by positivity) hn_abs
  have hnum_nonneg : 0 ≤ t / u ^ 2 :=
    div_nonneg ht (sq_nonneg u)
  have hsep :=
    four_pi_over_three_mul_abs_int_le_abs_modeSlope n hn hT ht ht' hu
  have hsq :
      ((4 * Real.pi / 3) * |(n : Real)|) ^ 2 ≤
        |zetaFirstApproximationModeSlope t n u| ^ 2 :=
    pow_le_pow_left₀ hbase_pos.le hsep 2
  calc
    ‖zetaFirstApproximationModeCurvature t n u‖ =
        ‖zetaFirstApproximationModeOscillation t n u *
        (Complex.I * ((t / u ^ 2 : Real) : Complex)) /
          (Complex.I *
            (zetaFirstApproximationModeSlope t n u : Complex)) ^ 2‖ := by
      rfl
    _ =
        (t / u ^ 2) /
          |zetaFirstApproximationModeSlope t n u| ^ 2 := by
      simp
      rw [abs_of_nonneg ht]
    _ ≤ (t / u ^ 2) /
        ((4 * Real.pi / 3) * |(n : Real)|) ^ 2 :=
      div_le_div_of_nonneg_left hnum_nonneg (sq_pos_of_pos hbase_pos) hsq

/-- The curvature correction is continuous wherever the mode slope is nonzero. -/
theorem continuousAt_zetaFirstApproximationModeCurvature
    {t u : Real} (n : Int) (hu : 0 < u)
    (hslope : zetaFirstApproximationModeSlope t n u ≠ 0) :
    ContinuousAt (zetaFirstApproximationModeCurvature t n) u := by
  have hosc :=
    hasDerivAt_zetaFirstApproximationModeOscillation (t := t) n hu
  have hu_ne : u ^ 2 ≠ 0 := pow_ne_zero 2 hu.ne'
  have hratioReal :=
    (hasDerivAt_const u t).div ((hasDerivAt_id u).pow 2) hu_ne
  have hratio := hratioReal.ofReal_comp.const_mul Complex.I
  have hslopeDeriv :=
    (hasDerivAt_zetaFirstApproximationModeSlope (t := t) n hu).ofReal_comp
  have hden := (hslopeDeriv.const_mul Complex.I).pow 2
  have hden_ne :
      (Complex.I * (zetaFirstApproximationModeSlope t n u : Complex)) ^ 2 ≠ 0 :=
    pow_ne_zero 2
      (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hslope))
  have hcurvature := (hosc.mul hratio).div hden hden_ne
  change ContinuousAt
    (fun v : Real => zetaFirstApproximationModeOscillation t n v *
        (Complex.I * ((t / v ^ 2 : Real) : Complex)) /
      (Complex.I * (zetaFirstApproximationModeSlope t n v : Complex)) ^ 2) u
  exact hcurvature.continuousAt

/--
Finite-interval integration by parts for one nonzero source Fourier mode.
It exposes exactly the endpoint term, differentiated amplitude, and curvature
correction used in the improper-tail estimate.
-/
theorem intervalIntegral_zetaFirstApproximationMode_integrationByParts
    {T t a b : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T)
    (ha : 3 * T / Real.pi ≤ a) (hab : a ≤ b) :
    ∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
        (zetaFirstApproximationModeOscillation t n u -
          zetaFirstApproximationModeCurvature t n u) =
      (zetaFirstApproximationTailAmplitude b : Complex) *
          zetaFirstApproximationModePrimitive t n b -
        (zetaFirstApproximationTailAmplitude a : Complex) *
          zetaFirstApproximationModePrimitive t n a -
        ∫ u in a..b,
          (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
            zetaFirstApproximationModePrimitive t n u := by
  have hcutoff_pos : 0 < 3 * T / Real.pi := by positivity
  have hx_data : ∀ x ∈ Set.uIcc a b,
      3 * T / Real.pi ≤ x ∧ 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨ha.trans hx.1, hcutoff_pos.trans_le (ha.trans hx.1)⟩
  have hAmplitudeDeriv : IntervalIntegrable
      (fun u : Real =>
        (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx_pos := (hx_data x hx).2
    have hp := Real.hasDerivAt_rpow_const
      (p := (-5 / 2 : Real)) (Or.inl hx_pos.ne')
    exact ((hp.const_mul (-3 / 2 : Real)).ofReal_comp).continuousAt
  have hPrimitiveDeriv : IntervalIntegrable
      (fun u : Real => zetaFirstApproximationModeOscillation t n u -
        zetaFirstApproximationModeCurvature t n u) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx_cut := (hx_data x hx).1
    have hx_pos := (hx_data x hx).2
    have hslope :=
      zetaFirstApproximationModeSlope_ne_zero n hn hT ht ht' hx_cut
    exact
      (hasDerivAt_zetaFirstApproximationModeOscillation (t := t) n hx_pos).continuousAt.sub
        (continuousAt_zetaFirstApproximationModeCurvature n hx_pos hslope)
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : Real => (zetaFirstApproximationTailAmplitude x : Complex))
    (v := zetaFirstApproximationModePrimitive t n)
    (u' := fun x : Real =>
      (((-3 / 2 : Real) * x ^ (-5 / 2 : Real) : Real) : Complex))
    (v' := fun x : Real => zetaFirstApproximationModeOscillation t n x -
      zetaFirstApproximationModeCurvature t n x)
    (fun x hx =>
      (hasDerivAt_zetaFirstApproximationTailAmplitude (hx_data x hx).2).ofReal_comp)
    (fun x hx =>
      hasDerivAt_zetaFirstApproximationModePrimitive n hn hT ht ht' (hx_data x hx).1)
    hAmplitudeDeriv hPrimitiveDeriv

/--
The integration-by-parts identity solved for the original oscillatory
integral.  Its three right-hand contributions are precisely the terms bounded
in the modewise tail estimate.
-/
theorem intervalIntegral_zetaFirstApproximationMode_eq_boundary_add_errors
    {T t a b : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T)
    (ha : 3 * T / Real.pi ≤ a) (hab : a ≤ b) :
    ∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeOscillation t n u =
      (zetaFirstApproximationTailAmplitude b : Complex) *
          zetaFirstApproximationModePrimitive t n b -
        (zetaFirstApproximationTailAmplitude a : Complex) *
          zetaFirstApproximationModePrimitive t n a -
        (∫ u in a..b,
          (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
            zetaFirstApproximationModePrimitive t n u) +
        (∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationModeCurvature t n u) := by
  have hcutoff_pos : 0 < 3 * T / Real.pi := by positivity
  have hx_data : ∀ x ∈ Set.uIcc a b,
      3 * T / Real.pi ≤ x ∧ 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨ha.trans hx.1, hcutoff_pos.trans_le (ha.trans hx.1)⟩
  have hAmplitude : ContinuousOn
      (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex))
      (Set.uIcc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    exact
      (hasDerivAt_zetaFirstApproximationTailAmplitude (hx_data x hx).2).ofReal_comp.continuousAt
  have hOscillation : ContinuousOn
      (zetaFirstApproximationModeOscillation t n) (Set.uIcc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    exact
      (hasDerivAt_zetaFirstApproximationModeOscillation
        (t := t) n (hx_data x hx).2).continuousAt
  have hCurvature : ContinuousOn
      (zetaFirstApproximationModeCurvature t n) (Set.uIcc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hslope :=
      zetaFirstApproximationModeSlope_ne_zero n hn hT ht ht' (hx_data x hx).1
    exact continuousAt_zetaFirstApproximationModeCurvature n (hx_data x hx).2 hslope
  have hAOscillation : IntervalIntegrable
      (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeOscillation t n u) volume a b :=
    (hAmplitude.mul hOscillation).intervalIntegrable
  have hACurvature : IntervalIntegrable
      (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeCurvature t n u) volume a b :=
    (hAmplitude.mul hCurvature).intervalIntegrable
  have hsplit :
      (∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
        (zetaFirstApproximationModeOscillation t n u -
          zetaFirstApproximationModeCurvature t n u)) =
        (∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationModeOscillation t n u) -
        ∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationModeCurvature t n u := by
    rw [← intervalIntegral.integral_sub hAOscillation hACurvature]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hibp :=
    intervalIntegral_zetaFirstApproximationMode_integrationByParts
      n hn hT ht ht' ha hab
  rw [hsplit] at hibp
  calc
    (∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeOscillation t n u) =
        ((∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationModeOscillation t n u) -
          ∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeCurvature t n u) +
          ∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeCurvature t n u := by abel
    _ = _ := by
      rw [hibp]

/-- The endpoint term is dominated by the decaying source amplitude. -/
theorem norm_zetaFirstApproximationTailAmplitude_mul_modePrimitive_le
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    ‖(zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModePrimitive t n u‖ ≤
      u ^ (-3 / 2 : Real) /
        ((4 * Real.pi / 3) * |(n : Real)|) := by
  have hu_pos : 0 < u := (by positivity : 0 < 3 * T / Real.pi).trans_le hu
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    zetaFirstApproximationTailAmplitude,
    abs_of_pos (Real.rpow_pos_of_pos hu_pos _)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [one_div] using
      norm_zetaFirstApproximationModePrimitive_le n hn hT ht ht' hu)
    (Real.rpow_nonneg hu_pos.le _)

/-- The upper endpoint contribution vanishes in the improper-tail limit. -/
theorem tendsto_zetaFirstApproximationTailAmplitude_mul_modePrimitive_atTop
    {T t : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) :
    Tendsto
      (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModePrimitive t n u)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ u : Real in atTop,
      ‖(zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationModePrimitive t n u‖ ≤
        u ^ (-3 / 2 : Real) /
          ((4 * Real.pi / 3) * |(n : Real)|) := by
    filter_upwards [eventually_ge_atTop (3 * T / Real.pi)] with u hu
    exact norm_zetaFirstApproximationTailAmplitude_mul_modePrimitive_le
      n hn hT ht ht' hu
  have hdecay : Tendsto (fun u : Real => u ^ (-(3 / 2 : Real)))
      atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hmajor := hdecay.div_const
    ((4 * Real.pi / 3) * |(n : Real)|)
  exact squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    hbound (by simpa only [neg_div, zero_div] using hmajor)

/-- The differentiated-amplitude error has an integrable `u⁻⁵ᐟ² / |n|` majorant. -/
theorem norm_zetaFirstApproximationTailAmplitudeDeriv_mul_modePrimitive_le
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    ‖(((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
        zetaFirstApproximationModePrimitive t n u‖ ≤
      ((3 / 2 : Real) * u ^ (-5 / 2 : Real)) *
        (1 / ((4 * Real.pi / 3) * |(n : Real)|)) := by
  have hu_pos : 0 < u := (by positivity : 0 < 3 * T / Real.pi).trans_le hu
  have hcoeff : |(-3 / 2 : Real)| = 3 / 2 := by norm_num
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, hcoeff,
    abs_of_pos (Real.rpow_pos_of_pos hu_pos _)]
  exact mul_le_mul_of_nonneg_left
    (norm_zetaFirstApproximationModePrimitive_le n hn hT ht ht' hu)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hu_pos.le _))

/--
The differentiated-amplitude contribution is absolutely integrable on every
admissible source tail.
-/
theorem integrableOn_zetaFirstApproximationTailAmplitudeDeriv_mul_modePrimitive
    {T t a : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (ha : 3 * T / Real.pi ≤ a) :
    IntegrableOn
      (fun u : Real =>
        (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
          zetaFirstApproximationModePrimitive t n u)
      (Set.Ioi a) := by
  have ha_pos : 0 < a := (by positivity : 0 < 3 * T / Real.pi).trans_le ha
  let c : Real := (3 / 2 : Real) *
    (1 / ((4 * Real.pi / 3) * |(n : Real)|))
  have hmajor : IntegrableOn
      (fun u : Real => c * u ^ (-5 / 2 : Real)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-5 / 2 : Real))
      (by norm_num) ha_pos).const_mul c
  rw [IntegrableOn] at hmajor ⊢
  refine hmajor.mono' ?_ ?_
  · have hAmplitudeDerivCont : ContinuousOn
        (fun u : Real =>
          (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex))
        (Set.Ioi a) := by
      intro u hu
      have hu_pos := ha_pos.trans hu
      have hp := Real.hasDerivAt_rpow_const
        (p := (-5 / 2 : Real)) (Or.inl hu_pos.ne')
      exact
        ((hp.const_mul (-3 / 2 : Real)).ofReal_comp).continuousAt.continuousWithinAt
    have hPrimitiveCont : ContinuousOn
        (zetaFirstApproximationModePrimitive t n) (Set.Ioi a) := by
      intro u hu
      have hu_cut : 3 * T / Real.pi ≤ u := ha.trans hu.le
      exact
        (hasDerivAt_zetaFirstApproximationModePrimitive
          n hn hT ht ht' hu_cut).continuousAt.continuousWithinAt
    exact (hAmplitudeDerivCont.mul hPrimitiveCont).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hbound :=
      norm_zetaFirstApproximationTailAmplitudeDeriv_mul_modePrimitive_le
        n hn hT ht ht' (ha.trans hu.le)
    simpa [c, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- The curvature error has an integrable `t u⁻⁷ᐟ² / |n|²` majorant. -/
theorem norm_zetaFirstApproximationTailAmplitude_mul_modeCurvature_le
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    ‖(zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeCurvature t n u‖ ≤
      (t / ((4 * Real.pi / 3) * |(n : Real)|) ^ 2) *
        u ^ (-7 / 2 : Real) := by
  have hu_pos : 0 < u := (by positivity : 0 < 3 * T / Real.pi).trans_le hu
  have hpow :
      u ^ (-3 / 2 : Real) / u ^ 2 = u ^ (-7 / 2 : Real) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_sub hu_pos]
    norm_num
  calc
    ‖(zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeCurvature t n u‖ =
        u ^ (-3 / 2 : Real) *
          ‖zetaFirstApproximationModeCurvature t n u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        zetaFirstApproximationTailAmplitude,
        abs_of_pos (Real.rpow_pos_of_pos hu_pos _)]
    _ ≤ u ^ (-3 / 2 : Real) *
        ((t / u ^ 2) /
          ((4 * Real.pi / 3) * |(n : Real)|) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (norm_zetaFirstApproximationModeCurvature_le n hn hT ht ht' hu)
        (Real.rpow_nonneg hu_pos.le _)
    _ = (t / ((4 * Real.pi / 3) * |(n : Real)|) ^ 2) *
        u ^ (-7 / 2 : Real) := by
      rw [← hpow]
      ring

/-- The curvature contribution is absolutely integrable on every admissible tail. -/
theorem integrableOn_zetaFirstApproximationTailAmplitude_mul_modeCurvature
    {T t a : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (ha : 3 * T / Real.pi ≤ a) :
    IntegrableOn
      (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeCurvature t n u)
      (Set.Ioi a) := by
  have ha_pos : 0 < a := (by positivity : 0 < 3 * T / Real.pi).trans_le ha
  let c : Real := t / ((4 * Real.pi / 3) * |(n : Real)|) ^ 2
  have hmajor : IntegrableOn
      (fun u : Real => c * u ^ (-7 / 2 : Real)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-7 / 2 : Real))
      (by norm_num) ha_pos).const_mul c
  rw [IntegrableOn] at hmajor ⊢
  refine hmajor.mono' ?_ ?_
  · have hAmplitudeCont : ContinuousOn
        (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex))
        (Set.Ioi a) := by
      intro u hu
      exact
        (hasDerivAt_zetaFirstApproximationTailAmplitude
          (ha_pos.trans hu)).ofReal_comp.continuousAt.continuousWithinAt
    have hCurvatureCont : ContinuousOn
        (zetaFirstApproximationModeCurvature t n) (Set.Ioi a) := by
      intro u hu
      have hu_cut : 3 * T / Real.pi ≤ u := ha.trans hu.le
      have hslope :=
        zetaFirstApproximationModeSlope_ne_zero n hn hT ht ht' hu_cut
      exact
        (continuousAt_zetaFirstApproximationModeCurvature
          n (ha_pos.trans hu) hslope).continuousWithinAt
    exact (hAmplitudeCont.mul hCurvatureCont).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact norm_zetaFirstApproximationTailAmplitude_mul_modeCurvature_le
      n hn hT ht ht' (ha.trans hu.le)

/-- The original normalized oscillatory mode is absolutely integrable. -/
theorem integrableOn_zetaFirstApproximationTailAmplitude_mul_modeOscillation
    {a t : Real} (n : Int) (ha : 0 < a) :
    IntegrableOn
      (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeOscillation t n u)
      (Set.Ioi a) := by
  have hmajor : IntegrableOn (fun u : Real => u ^ (-3 / 2 : Real))
      (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  rw [IntegrableOn] at hmajor ⊢
  refine hmajor.mono' ?_ ?_
  · have hAmplitudeCont : ContinuousOn
        (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex))
        (Set.Ioi a) := by
      intro u hu
      exact
        (hasDerivAt_zetaFirstApproximationTailAmplitude
          (ha.trans hu)).ofReal_comp.continuousAt.continuousWithinAt
    have hOscillationCont : ContinuousOn
        (zetaFirstApproximationModeOscillation t n) (Set.Ioi a) := by
      intro u hu
      exact
        (hasDerivAt_zetaFirstApproximationModeOscillation
          (t := t) n (ha.trans hu)).continuousAt.continuousWithinAt
    exact (hAmplitudeCont.mul hOscillationCont).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu_pos := ha.trans hu
    simp [zetaFirstApproximationTailAmplitude,
      abs_of_pos (Real.rpow_pos_of_pos hu_pos _)]

/--
Improper-tail integration by parts for one source Fourier mode.  Both error
integrals are absolutely convergent and the upper boundary has disappeared.
-/
theorem integral_Ioi_zetaFirstApproximationMode_eq_boundary_add_errors
    {T t a : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (ha : 3 * T / Real.pi ≤ a) :
    (∫ u in Set.Ioi a, (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeOscillation t n u) =
      -(zetaFirstApproximationTailAmplitude a : Complex) *
          zetaFirstApproximationModePrimitive t n a -
        (∫ u in Set.Ioi a,
          (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
            zetaFirstApproximationModePrimitive t n u) +
        (∫ u in Set.Ioi a,
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeCurvature t n u) := by
  have ha_pos : 0 < a := (by positivity : 0 < 3 * T / Real.pi).trans_le ha
  have hOriginal :=
    integrableOn_zetaFirstApproximationTailAmplitude_mul_modeOscillation
      (t := t) n ha_pos
  have hAmplitudeError :=
    integrableOn_zetaFirstApproximationTailAmplitudeDeriv_mul_modePrimitive
      n hn hT ht ht' ha
  have hCurvatureError :=
    integrableOn_zetaFirstApproximationTailAmplitude_mul_modeCurvature
      n hn hT ht ht' ha
  have hOriginalLimit := intervalIntegral_tendsto_integral_Ioi
    (f := fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex) *
      zetaFirstApproximationModeOscillation t n u)
    a hOriginal tendsto_id
  have hAmplitudeErrorLimit := intervalIntegral_tendsto_integral_Ioi
    (f := fun u : Real =>
      (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
        zetaFirstApproximationModePrimitive t n u)
    a hAmplitudeError tendsto_id
  have hCurvatureErrorLimit := intervalIntegral_tendsto_integral_Ioi
    (f := fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex) *
      zetaFirstApproximationModeCurvature t n u)
    a hCurvatureError tendsto_id
  have hUpperBoundary :=
    tendsto_zetaFirstApproximationTailAmplitude_mul_modePrimitive_atTop
      n hn hT ht ht'
  have hLowerBoundary : Tendsto
      (fun _ : Real => (zetaFirstApproximationTailAmplitude a : Complex) *
        zetaFirstApproximationModePrimitive t n a)
      atTop
      (𝓝 ((zetaFirstApproximationTailAmplitude a : Complex) *
        zetaFirstApproximationModePrimitive t n a)) :=
    tendsto_const_nhds
  have hRightLimit : Tendsto
      (fun b : Real =>
        (zetaFirstApproximationTailAmplitude b : Complex) *
            zetaFirstApproximationModePrimitive t n b -
          (zetaFirstApproximationTailAmplitude a : Complex) *
            zetaFirstApproximationModePrimitive t n a -
          (∫ u in a..b,
            (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
              zetaFirstApproximationModePrimitive t n u) +
          (∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeCurvature t n u))
      atTop
      (𝓝 (0 -
          (zetaFirstApproximationTailAmplitude a : Complex) *
            zetaFirstApproximationModePrimitive t n a -
          (∫ u in Set.Ioi a,
            (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
              zetaFirstApproximationModePrimitive t n u) +
          (∫ u in Set.Ioi a,
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationModeCurvature t n u))) :=
    ((hUpperBoundary.sub hLowerBoundary).sub hAmplitudeErrorLimit).add
      hCurvatureErrorLimit
  have hfinite : ∀ᶠ b : Real in atTop,
      (∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeOscillation t n u) =
        (zetaFirstApproximationTailAmplitude b : Complex) *
            zetaFirstApproximationModePrimitive t n b -
          (zetaFirstApproximationTailAmplitude a : Complex) *
            zetaFirstApproximationModePrimitive t n a -
          (∫ u in a..b,
            (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
              zetaFirstApproximationModePrimitive t n u) +
          (∫ u in a..b, (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeCurvature t n u) := by
    filter_upwards [eventually_ge_atTop a] with b hab
    exact intervalIntegral_zetaFirstApproximationMode_eq_boundary_add_errors
      n hn hT ht ht' ha hab
  have hlimitEq :=
    tendsto_nhds_unique (hOriginalLimit.congr' hfinite) hRightLimit
  simpa only [zero_sub, neg_mul] using hlimitEq

/-- Exact integrated majorant for the differentiated-amplitude error. -/
theorem norm_integral_Ioi_zetaFirstApproximationTailAmplitudeDeriv_mul_modePrimitive_le
    {T t a : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (ha : 3 * T / Real.pi ≤ a) :
    ‖∫ u in Set.Ioi a,
        (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
          zetaFirstApproximationModePrimitive t n u‖ ≤
      a ^ (-3 / 2 : Real) *
        (1 / ((4 * Real.pi / 3) * |(n : Real)|)) := by
  have ha_pos : 0 < a := (by positivity : 0 < 3 * T / Real.pi).trans_le ha
  let c : Real := (3 / 2 : Real) *
    (1 / ((4 * Real.pi / 3) * |(n : Real)|))
  have hmajor : IntegrableOn
      (fun u : Real => c * u ^ (-5 / 2 : Real)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-5 / 2 : Real))
      (by norm_num) ha_pos).const_mul c
  have hbound := MeasureTheory.norm_integral_le_of_norm_le hmajor
    (μ := volume.restrict (Set.Ioi a))
    (f := fun u : Real =>
      (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
        zetaFirstApproximationModePrimitive t n u)
    (g := fun u : Real => c * u ^ (-5 / 2 : Real))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hpoint :=
        norm_zetaFirstApproximationTailAmplitudeDeriv_mul_modePrimitive_le
          n hn hT ht ht' (ha.trans hu.le)
      simpa [c, mul_assoc, mul_left_comm, mul_comm] using hpoint)
  calc
    ‖∫ u in Set.Ioi a,
        (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
          zetaFirstApproximationModePrimitive t n u‖ ≤
        ∫ u in Set.Ioi a, c * u ^ (-5 / 2 : Real) := hbound
    _ = a ^ (-3 / 2 : Real) *
        (1 / ((4 * Real.pi / 3) * |(n : Real)|)) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (a := (-5 / 2 : Real)) (by norm_num) ha_pos]
      dsimp [c]
      norm_num
      ring

/-- Exact integrated majorant for the curvature error. -/
theorem norm_integral_Ioi_zetaFirstApproximationTailAmplitude_mul_modeCurvature_le
    {T t a : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (ha : 3 * T / Real.pi ≤ a) :
    ‖∫ u in Set.Ioi a,
        (zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationModeCurvature t n u‖ ≤
      ((2 / 5 : Real) * t /
          ((4 * Real.pi / 3) * |(n : Real)|) ^ 2) *
        a ^ (-5 / 2 : Real) := by
  have ha_pos : 0 < a := (by positivity : 0 < 3 * T / Real.pi).trans_le ha
  let c : Real := t / ((4 * Real.pi / 3) * |(n : Real)|) ^ 2
  have hmajor : IntegrableOn
      (fun u : Real => c * u ^ (-7 / 2 : Real)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-7 / 2 : Real))
      (by norm_num) ha_pos).const_mul c
  have hbound := MeasureTheory.norm_integral_le_of_norm_le hmajor
    (μ := volume.restrict (Set.Ioi a))
    (f := fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex) *
      zetaFirstApproximationModeCurvature t n u)
    (g := fun u : Real => c * u ^ (-7 / 2 : Real))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_zetaFirstApproximationTailAmplitude_mul_modeCurvature_le
        n hn hT ht ht' (ha.trans hu.le))
  calc
    ‖∫ u in Set.Ioi a,
        (zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationModeCurvature t n u‖ ≤
        ∫ u in Set.Ioi a, c * u ^ (-7 / 2 : Real) := hbound
    _ = ((2 / 5 : Real) * t /
          ((4 * Real.pi / 3) * |(n : Real)|) ^ 2) *
        a ^ (-5 / 2 : Real) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (a := (-7 / 2 : Real)) (by norm_num) ha_pos]
      dsimp [c]
      norm_num
      ring

/--
Complete quantitative improper-tail estimate for one nonzero Fourier mode.
The first term gains `|n|⁻¹`; the curvature term gains `|n|⁻²`.
-/
theorem norm_integral_Ioi_zetaFirstApproximationMode_le
    {T t a : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (ha : 3 * T / Real.pi ≤ a) :
    ‖∫ u in Set.Ioi a,
        (zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationModeOscillation t n u‖ ≤
      2 * a ^ (-3 / 2 : Real) *
          (1 / ((4 * Real.pi / 3) * |(n : Real)|)) +
        ((2 / 5 : Real) * t /
            ((4 * Real.pi / 3) * |(n : Real)|) ^ 2) *
          a ^ (-5 / 2 : Real) := by
  have hidentity :=
    integral_Ioi_zetaFirstApproximationMode_eq_boundary_add_errors
      n hn hT ht ht' ha
  have hEndpoint :=
    norm_zetaFirstApproximationTailAmplitude_mul_modePrimitive_le
      n hn hT ht ht' ha
  have hAmplitudeError :=
    norm_integral_Ioi_zetaFirstApproximationTailAmplitudeDeriv_mul_modePrimitive_le
      n hn hT ht ht' ha
  have hCurvatureError :=
    norm_integral_Ioi_zetaFirstApproximationTailAmplitude_mul_modeCurvature_le
      n hn hT ht ht' ha
  rw [hidentity]
  calc
    ‖-(zetaFirstApproximationTailAmplitude a : Complex) *
          zetaFirstApproximationModePrimitive t n a -
        (∫ u in Set.Ioi a,
          (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
            zetaFirstApproximationModePrimitive t n u) +
        (∫ u in Set.Ioi a,
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeCurvature t n u)‖ ≤
        ‖(zetaFirstApproximationTailAmplitude a : Complex) *
          zetaFirstApproximationModePrimitive t n a‖ +
        ‖∫ u in Set.Ioi a,
          (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
            zetaFirstApproximationModePrimitive t n u‖ +
        ‖∫ u in Set.Ioi a,
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeCurvature t n u‖ := by
      calc
        _ ≤ ‖-(zetaFirstApproximationTailAmplitude a : Complex) *
              zetaFirstApproximationModePrimitive t n a -
            (∫ u in Set.Ioi a,
              (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
                zetaFirstApproximationModePrimitive t n u)‖ +
            ‖∫ u in Set.Ioi a,
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationModeCurvature t n u‖ := norm_add_le _ _
        _ ≤ _ := by
          gcongr
          calc
            ‖-(zetaFirstApproximationTailAmplitude a : Complex) *
                zetaFirstApproximationModePrimitive t n a -
              (∫ u in Set.Ioi a,
                (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
                  zetaFirstApproximationModePrimitive t n u)‖ ≤
                ‖-(zetaFirstApproximationTailAmplitude a : Complex) *
                  zetaFirstApproximationModePrimitive t n a‖ +
                ‖∫ u in Set.Ioi a,
                  (((-3 / 2 : Real) * u ^ (-5 / 2 : Real) : Real) : Complex) *
                    zetaFirstApproximationModePrimitive t n u‖ := norm_sub_le _ _
            _ = _ := by rw [neg_mul, norm_neg]
    _ ≤ a ^ (-3 / 2 : Real) /
          ((4 * Real.pi / 3) * |(n : Real)|) +
        a ^ (-3 / 2 : Real) *
          (1 / ((4 * Real.pi / 3) * |(n : Real)|)) +
        ((2 / 5 : Real) * t /
            ((4 * Real.pi / 3) * |(n : Real)|) ^ 2) *
          a ^ (-5 / 2 : Real) := by
      exact add_le_add (add_le_add hEndpoint hAmplitudeError) hCurvatureError
    _ = 2 * a ^ (-3 / 2 : Real) *
          (1 / ((4 * Real.pi / 3) * |(n : Real)|)) +
        ((2 / 5 : Real) * t /
            ((4 * Real.pi / 3) * |(n : Real)|) ^ 2) *
          a ^ (-5 / 2 : Real) := by
      rw [div_eq_mul_inv, one_div]
      ring

/--
The sawtooth coefficient and the nonresonant phase denominator together are
bounded by the summable inverse-square mode majorant.
-/
theorem nonzeroMode_reciprocal_le_invSq_majorant
    {T t u : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (hu : 3 * T / Real.pi ≤ u) :
    1 / (|(n : Real)| *
        |(n : Real) - deriv (zetaFirstApproximationPhase t) u|) ≤
      (3 / 2 : Real) * (1 / |(n : Real)| ^ 2) := by
  have hsep :=
    two_thirds_mul_abs_int_le_abs_int_sub_phaseDeriv n hn hT ht ht' hu
  have hn_pos : 0 < |(n : Real)| := by
    rw [abs_pos]
    exact_mod_cast hn
  have hden :
      (2 / 3 : Real) * |(n : Real)| ^ 2 ≤
        |(n : Real)| *
          |(n : Real) - deriv (zetaFirstApproximationPhase t) u| := by
    calc
      (2 / 3 : Real) * |(n : Real)| ^ 2 =
          |(n : Real)| * ((2 / 3 : Real) * |(n : Real)|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsep (abs_nonneg _)
  have hinv := one_div_le_one_div_of_le
    (mul_pos (by norm_num : (0 : Real) < 2 / 3) (sq_pos_of_pos hn_pos)) hden
  calc
    _ ≤ 1 / ((2 / 3 : Real) * |(n : Real)| ^ 2) := hinv
    _ = (3 / 2 : Real) * (1 / |(n : Real)| ^ 2) := by
      field_simp [hn_pos.ne']

/-- The inverse-square majorant for all integer modes is summable. -/
theorem summable_zetaFirstApproximation_invSq_majorant :
    Summable (fun n : Int => (3 / 2 : Real) * (1 / |(n : Real)| ^ 2)) := by
  apply Summable.mul_left
  simpa only [sq_abs] using
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)

/-- The source logarithmic phase has decreasing derivative. -/
theorem antitoneOn_deriv_zetaFirstApproximationPhase
    {t : Real} (ht : 0 ≤ t) :
    AntitoneOn (deriv (zetaFirstApproximationPhase t)) (Ioi 0) := by
  intro a ha b hb hab
  rw [deriv_zetaFirstApproximationPhase ha,
    deriv_zetaFirstApproximationPhase hb]
  have hden_pos : 0 < 2 * Real.pi * a := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ha
  have hden_le : 2 * Real.pi * a ≤ 2 * Real.pi * b := by gcongr
  exact div_le_div_of_nonneg_left ht hden_pos hden_le

/-- The fixed critical-line amplitude in Titchmarsh's weighted lemma. -/
def zetaFirstApproximationAmplitude (u : Real) : Real :=
  u ^ (-(1 / 2 : Real))

/-- The absolute derivative of the critical-line amplitude is explicit. -/
theorem abs_deriv_zetaFirstApproximationAmplitude
    {u : Real} (hu : 0 < u) :
    |deriv zetaFirstApproximationAmplitude u| =
      (1 / 2 : Real) * u ^ (-(3 / 2 : Real)) := by
  rw [show deriv zetaFirstApproximationAmplitude u =
      -(1 / 2 : Real) * u ^ (-(3 / 2 : Real)) by
    unfold zetaFirstApproximationAmplitude
    rw [Real.deriv_rpow_const]
    congr 1
    ring_nf]
  rw [abs_mul, abs_neg,
    abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : Real)),
    abs_of_pos (Real.rpow_pos_of_pos hu _)]

/-- Both the amplitude and the absolute value of its derivative decrease. -/
theorem zetaFirstApproximationAmplitude_sourceMonotonicity :
    AntitoneOn zetaFirstApproximationAmplitude (Ioi 0) ∧
      AntitoneOn (fun u => |deriv zetaFirstApproximationAmplitude u|) (Ioi 0) := by
  constructor
  · change AntitoneOn (fun u : Real => u ^ (-(1 / 2 : Real))) (Ioi 0)
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
  · intro a ha b hb hab
    change |deriv zetaFirstApproximationAmplitude b| ≤
      |deriv zetaFirstApproximationAmplitude a|
    rw [abs_deriv_zetaFirstApproximationAmplitude ha,
      abs_deriv_zetaFirstApproximationAmplitude hb]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hab
        (by norm_num : -(3 / 2 : Real) ≤ 0))
      (by norm_num)

/--
The first Bernoulli sawtooth on the unit additive circle, with the value at
the integer class chosen from the right endpoint.  This choice changes only
one point and is the one naturally supplied by the interval lift used in the
`L²` Fourier theory.
-/
def zetaFirstApproximationSawtooth : UnitAddCircle → Complex :=
  AddCircle.liftIoc 1 0 (fun u : Real => (bernoulliFun 1 u : Complex))

/-- The same centered sawtooth on the real line, using the fractional-part representative. -/
def zetaFirstApproximationRealSawtooth (u : Real) : Complex :=
  (bernoulliFun 1 (Int.fract u) : Complex)

/-- The real representative of the source sawtooth is measurable. -/
theorem measurable_zetaFirstApproximationRealSawtooth :
    Measurable zetaFirstApproximationRealSawtooth := by
  exact Complex.continuous_ofReal.measurable.comp
    ((continuous_bernoulliFun 1).measurable.comp measurable_fract)

/-- The centered source sawtooth is uniformly bounded by one half. -/
theorem norm_zetaFirstApproximationRealSawtooth_le_half (u : Real) :
    ‖zetaFirstApproximationRealSawtooth u‖ ≤ 1 / 2 := by
  rw [zetaFirstApproximationRealSawtooth, Complex.norm_real,
    Real.norm_eq_abs, bernoulliFun_one, abs_le]
  constructor
  · linarith [Int.fract_nonneg u]
  · linarith [Int.fract_lt_one u]

/-- Away from integer endpoints, the real and additive-circle sawtooth representatives agree. -/
theorem zetaFirstApproximationSawtooth_coe_eq_realSawtooth
    {u : Real} (hu : Int.fract u ≠ 0) :
    zetaFirstApproximationSawtooth (u : UnitAddCircle) =
      zetaFirstApproximationRealSawtooth u := by
  have hfract : Int.fract u ∈ Ioc (0 : Real) (0 + 1) := by
    constructor
    · exact lt_of_le_of_ne (Int.fract_nonneg u) (Ne.symm hu)
    · simpa using (Int.fract_lt_one u).le
  rw [← AddCircle.coe_fract u, zetaFirstApproximationSawtooth,
    AddCircle.liftIoc_coe_apply hfract,
    zetaFirstApproximationRealSawtooth]

/-- The two sawtooth representatives agree almost everywhere on the real line. -/
theorem ae_zetaFirstApproximationSawtooth_coe_eq_realSawtooth :
    (fun u : Real => zetaFirstApproximationSawtooth (u : UnitAddCircle)) =ᵐ[volume]
      zetaFirstApproximationRealSawtooth := by
  have hzero : volume (Set.range ((↑) : Int → Real)) = 0 :=
    (Set.countable_range ((↑) : Int → Real)).measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hzero] with u hu
  apply zetaFirstApproximationSawtooth_coe_eq_realSawtooth
  intro hfract
  exact hu ((Int.fract_eq_zero_iff.mp hfract))

/-- The actual normalized sawtooth remainder integrand before Fourier reconstruction. -/
def zetaFirstApproximationSawtoothTailIntegrand (t u : Real) : Complex :=
  zetaFirstApproximationRealSawtooth u *
    (zetaFirstApproximationTailAmplitude u : Complex) *
      zetaFirstApproximationTailTwist t u

/-- The reconstructed integrand is exactly the centered Euler kernel on the critical line. -/
theorem zetaFirstApproximationSawtoothTailIntegrand_eq_cpow
    (t : Real) {u : Real} (hu : 0 < u) :
    zetaFirstApproximationSawtoothTailIntegrand t u =
      zetaFirstApproximationRealSawtooth u *
        (u : Complex) ^
          (-(((1 / 2 : Real) : Complex) + t * Complex.I) - 1) := by
  rw [zetaFirstApproximationSawtoothTailIntegrand, mul_assoc,
    zetaFirstApproximationTailWeight_eq_cpow t hu]

/-- The centered Euler kernel is absolutely integrable whenever the complex exponent has positive real part. -/
theorem integrableOn_zetaFirstApproximationRealSawtooth_mul_cpow
    {s : Complex} {a : Real} (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn
      (fun u : Real => zetaFirstApproximationRealSawtooth u *
        (u : Complex) ^ (-(s + 1))) (Ioi a) := by
  let p : Real := -(s.re + 1)
  have hp : p < -1 := by dsimp [p]; linarith
  have hmajorant : IntegrableOn (fun u : Real => u ^ p) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt hp ha
  change Integrable
    (fun u : Real => zetaFirstApproximationRealSawtooth u *
      (u : Complex) ^ (-(s + 1))) (volume.restrict (Ioi a))
  change Integrable (fun u : Real => u ^ p) (volume.restrict (Ioi a)) at hmajorant
  refine Integrable.mono' hmajorant ?_ ?_
  · have hpow : ContinuousOn (fun u : Real => (u : Complex) ^ (-(s + 1))) (Ioi a) := by
      intro u hu
      exact (continuousAt_ofReal_cpow_const _ _
        (Or.inr (ha.trans hu).ne')).continuousWithinAt
    exact measurable_zetaFirstApproximationRealSawtooth.aestronglyMeasurable.mul
      (hpow.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := ha.trans hu
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    have hp_eq : (-(s + 1)).re = p := by simp [p]
    rw [hp_eq]
    have hpow_nonneg : 0 ≤ u ^ p := Real.rpow_nonneg hu_pos.le p
    nlinarith [norm_zetaFirstApproximationRealSawtooth_le_half u]

/-- A logarithmic derivative of a positive-half-plane Euler kernel remains integrable. -/
theorem integrableOn_log_mul_rpow_Ioi_one
    {c : Real} (hc : 0 < c) :
    IntegrableOn (fun u : Real => Real.log u * u ^ (-c - 1)) (Ioi (1 : Real)) := by
  let ε : Real := c / 2
  let q : Real := -c / 2 - 1
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hq : q < -1 := by dsimp [q]; linarith
  have hmajorant : IntegrableOn
      (fun u : Real => (1 / ε) * u ^ q) (Ioi (1 : Real)) :=
    (integrableOn_Ioi_rpow_of_lt hq zero_lt_one).const_mul (1 / ε)
  change Integrable (fun u : Real => Real.log u * u ^ (-c - 1))
    (volume.restrict (Ioi (1 : Real)))
  change Integrable (fun u : Real => (1 / ε) * u ^ q)
    (volume.restrict (Ioi (1 : Real))) at hmajorant
  refine Integrable.mono' hmajorant ?_ ?_
  · have hlog : ContinuousOn Real.log (Ioi (1 : Real)) :=
      Real.continuousOn_log.mono fun u hu => (zero_lt_one.trans hu).ne'
    have hpow : ContinuousOn (fun u : Real => u ^ (-c - 1)) (Ioi (1 : Real)) :=
      continuousOn_id.rpow_const fun u hu => Or.inl (zero_lt_one.trans hu).ne'
    exact (hlog.mul hpow).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := zero_lt_one.trans hu
    have hlog_pos : 0 < Real.log u := Real.log_pos hu
    have hpow_pos : 0 < u ^ (-c - 1) := Real.rpow_pos_of_pos hu_pos _
    have hlog_le : Real.log u ≤ u ^ ε / ε := Real.log_le_rpow_div hu_pos.le hε
    calc
      ‖Real.log u * u ^ (-c - 1)‖ = Real.log u * u ^ (-c - 1) := by
        rw [Real.norm_eq_abs, abs_of_pos (mul_pos hlog_pos hpow_pos)]
      Real.log u * u ^ (-c - 1) ≤ (u ^ ε / ε) * u ^ (-c - 1) :=
        mul_le_mul_of_nonneg_right hlog_le hpow_pos.le
      _ = (1 / ε) * (u ^ ε * u ^ (-c - 1)) := by ring
      _ = (1 / ε) * u ^ (ε + (-c - 1)) := by rw [Real.rpow_add hu_pos]
      _ = (1 / ε) * u ^ q := by
        congr 2
        dsimp [q, ε]
        ring

/-- The specific Euler-sawtooth remainder is complex differentiable on the positive half-plane. -/
theorem differentiableAt_zetaFirstApproximationEulerSawtoothIntegral
    {s : Complex} (hs : 0 < s.re) :
    DifferentiableAt Complex
      (fun z : Complex => ∫ u in Ioi (1 : Real),
        zetaFirstApproximationRealSawtooth u *
          (u : Complex) ^ (-(z + 1))) s := by
  let δ : Real := s.re / 4
  let c : Real := s.re / 2
  let F : Complex → Real → Complex := fun z u =>
    zetaFirstApproximationRealSawtooth u *
      (u : Complex) ^ (-(z + 1))
  let F' : Complex → Real → Complex := fun z u =>
    zetaFirstApproximationRealSawtooth u *
      ((u : Complex) ^ (-(z + 1)) * (Real.log u : Complex) * (-1))
  let bound : Real → Real := fun u => Real.log u * u ^ (-c - 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hre {z : Complex} (hz : z ∈ Metric.ball s δ) : c ≤ z.re := by
    have hdist : dist z s < δ := hz
    have hre_norm : |z.re - s.re| ≤ ‖z - s‖ := by
      simpa only [sub_re] using Complex.abs_re_le_norm (z - s)
    have hnorm : ‖z - s‖ = dist z s := by rw [dist_eq]
    rw [hnorm] at hre_norm
    have hlower : -(dist z s) ≤ z.re - s.re :=
      (neg_le_neg hre_norm).trans (neg_abs_le (z.re - s.re))
    dsimp [c, δ] at hdist ⊢
    nlinarith
  have hF_meas : ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (F z) (volume.restrict (Ioi (1 : Real))) := by
    filter_upwards [Metric.ball_mem_nhds s hδ] with z hz
    exact (integrableOn_zetaFirstApproximationRealSawtooth_mul_cpow
      (hc.trans_le (hre hz)) zero_lt_one).aestronglyMeasurable
  have hF_int : Integrable (F s) (volume.restrict (Ioi (1 : Real))) :=
    integrableOn_zetaFirstApproximationRealSawtooth_mul_cpow hs zero_lt_one
  have hF'_meas : AEStronglyMeasurable (F' s)
      (volume.restrict (Ioi (1 : Real))) := by
    have hpow : ContinuousOn
        (fun u : Real => (u : Complex) ^ (-(s + 1))) (Ioi (1 : Real)) := by
      intro u hu
      exact (continuousAt_ofReal_cpow_const _ _
        (Or.inr (zero_lt_one.trans hu).ne')).continuousWithinAt
    have hlog : ContinuousOn (fun u : Real => (Real.log u : Complex))
        (Ioi (1 : Real)) :=
      Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono fun u hu => (zero_lt_one.trans hu).ne')
    exact (measurable_zetaFirstApproximationRealSawtooth.aestronglyMeasurable.mul
      (((hpow.mul hlog).mul continuousOn_const).aestronglyMeasurable measurableSet_Ioi))
  have hbound_int : Integrable bound (volume.restrict (Ioi (1 : Real))) :=
    integrableOn_log_mul_rpow_Ioi_one hc
  have h_bound : ∀ᵐ u ∂volume.restrict (Ioi (1 : Real)),
      ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu z hz
    have hu_pos : 0 < u := zero_lt_one.trans hu
    have hlog_nonneg : 0 ≤ Real.log u := (Real.log_pos hu).le
    have hzre : c ≤ z.re := hre hz
    have hpow_le : u ^ (-(z + 1)).re ≤ u ^ (-c - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hu.le
      have hexp : (-(z + 1)).re = -z.re - 1 := by simp; ring
      rw [hexp]
      linarith
    simp only [F']
    rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_one,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog_nonneg,
      Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    have hsaw_le : ‖zetaFirstApproximationRealSawtooth u‖ ≤ 1 :=
      (norm_zetaFirstApproximationRealSawtooth_le_half u).trans (by norm_num)
    calc
      ‖zetaFirstApproximationRealSawtooth u‖ *
          (u ^ (-(z + 1)).re * Real.log u) ≤
          1 * (u ^ (-(z + 1)).re * Real.log u) :=
        mul_le_mul_of_nonneg_right hsaw_le
          (mul_nonneg (Real.rpow_nonneg hu_pos.le _) hlog_nonneg)
      _ ≤ 1 * (u ^ (-c - 1) * Real.log u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow_le hlog_nonneg) zero_le_one
      _ = Real.log u * u ^ (-c - 1) := by ring
  have h_diff : ∀ᵐ u ∂volume.restrict (Ioi (1 : Real)),
      ∀ z ∈ Metric.ball s δ, HasDerivAt (F · u) (F' z u) z := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu z hz
    have hu_pos : 0 < u := zero_lt_one.trans hu
    have huC : (u : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hexp : HasDerivAt (fun w : Complex => -(w + 1)) (-1) z :=
      ((hasDerivAt_id z).add_const 1).neg
    have hpow := hexp.const_cpow (Or.inl huC)
    have hmul := hpow.const_mul (zetaFirstApproximationRealSawtooth u)
    rw [← Complex.ofReal_log hu_pos.le] at hmul
    simpa only [F, F'] using hmul
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (1 : Real))) (F := F) (F' := F')
    (Metric.ball_mem_nhds s hδ) hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2.differentiableAt

/-- The sawtooth remainder integrand is absolutely integrable on every positive tail. -/
theorem integrableOn_zetaFirstApproximationSawtoothTailIntegrand
    (t : Real) {a : Real} (ha : 0 < a) :
    IntegrableOn (zetaFirstApproximationSawtoothTailIntegrand t) (Ioi a) := by
  have hmajorant : IntegrableOn
      zetaFirstApproximationTailAmplitude
      (Ioi a) := by
    exact integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-3 / 2 : Real) < -1) ha
  change Integrable (zetaFirstApproximationSawtoothTailIntegrand t)
    (volume.restrict (Ioi a))
  change Integrable zetaFirstApproximationTailAmplitude
    (volume.restrict (Ioi a)) at hmajorant
  refine Integrable.mono' hmajorant ?_ ?_
  · have hamp : ContinuousOn zetaFirstApproximationTailAmplitude (Ioi a) := by
      exact continuousOn_id.rpow_const fun u hu =>
        Or.inl (ne_of_gt (ha.trans hu))
    have hampC : AEStronglyMeasurable
        (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex))
        (volume.restrict (Ioi a)) :=
      (Complex.continuous_ofReal.comp_continuousOn hamp).aestronglyMeasurable
        measurableSet_Ioi
    exact ((measurable_zetaFirstApproximationRealSawtooth.aestronglyMeasurable.mul
      hampC).mul (measurable_zetaFirstApproximationTailTwist t).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [zetaFirstApproximationSawtoothTailIntegrand, norm_mul, norm_mul,
      norm_zetaFirstApproximationTailTwist, mul_one, Complex.norm_real,
      Real.norm_eq_abs, zetaFirstApproximationTailAmplitude, abs_of_pos
        (Real.rpow_pos_of_pos (ha.trans hu) (-3 / 2 : Real))]
    nlinarith [norm_zetaFirstApproximationRealSawtooth_le_half u,
      Real.rpow_nonneg (ha.trans hu).le (-3 / 2 : Real)]

/-- Every Fourier monomial times the common source tail weight is integrable. -/
theorem integrableOn_zetaFirstApproximationFourierTailWeight
    (t : Real) (n : Int) {a : Real} (ha : 0 < a) :
    IntegrableOn
      (fun u : Real =>
        fourier n (u : UnitAddCircle) *
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationTailTwist t u)
      (Ioi a) := by
  have hmajorant : IntegrableOn zetaFirstApproximationTailAmplitude (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-3 / 2 : Real) < -1) ha
  change Integrable
    (fun u : Real =>
      fourier n (u : UnitAddCircle) *
        (zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationTailTwist t u)
    (volume.restrict (Ioi a))
  change Integrable zetaFirstApproximationTailAmplitude
    (volume.restrict (Ioi a)) at hmajorant
  refine Integrable.mono' hmajorant ?_ ?_
  · have hamp : ContinuousOn zetaFirstApproximationTailAmplitude (Ioi a) := by
      exact continuousOn_id.rpow_const fun u hu =>
        Or.inl (ne_of_gt (ha.trans hu))
    have hampC : AEStronglyMeasurable
        (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex))
        (volume.restrict (Ioi a)) :=
      (Complex.continuous_ofReal.comp_continuousOn hamp).aestronglyMeasurable
        measurableSet_Ioi
    have hfourier : Measurable
        (fun u : Real => fourier n (u : UnitAddCircle)) :=
      (fourier n).continuous.measurable.comp AddCircle.measurable_mk'
    exact ((hfourier.aestronglyMeasurable.mul hampC).mul
      (measurable_zetaFirstApproximationTailTwist t).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [norm_mul, norm_mul, norm_zetaFirstApproximationTailTwist, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      zetaFirstApproximationTailAmplitude,
      abs_of_pos (Real.rpow_pos_of_pos (ha.trans hu) (-3 / 2 : Real))]
    rw [fourier_coe_apply, Complex.norm_exp]
    simp

/-- Replacing the real sawtooth by its circle representative does not change the tail integral. -/
theorem integral_Ioi_zetaFirstApproximationSawtooth_coe_eq_realSawtooth
    (t a : Real) :
    (∫ u in Ioi a,
        zetaFirstApproximationSawtooth (u : UnitAddCircle) *
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationTailTwist t u) =
      ∫ u in Ioi a, zetaFirstApproximationSawtoothTailIntegrand t u := by
  apply integral_congr_ae
  have hae :
      (fun u : Real => zetaFirstApproximationSawtooth (u : UnitAddCircle))
        =ᵐ[volume.restrict (Ioi a)] zetaFirstApproximationRealSawtooth :=
    Eventually.filter_mono
    (ae_mono Measure.restrict_le_self)
    ae_zetaFirstApproximationSawtooth_coe_eq_realSawtooth
  filter_upwards [hae] with u hu
  simp only [zetaFirstApproximationSawtoothTailIntegrand, hu]

/--
The conjugated source weight on one period cell, lifted to the unit additive
circle.  Pairing this function with the sawtooth Fourier series produces the
weighted source integral on that cell.
-/
def zetaFirstApproximationCellTest (t a : Real) : UnitAddCircle → Complex :=
  AddCircle.liftIoc 1 a (fun u : Real =>
    conj ((zetaFirstApproximationTailAmplitude u : Complex) *
      zetaFirstApproximationTailTwist t u))

/-- The source weight on every positive unit cell is an admissible `L²` test. -/
theorem zetaFirstApproximationCellTest_memLp
    (t : Real) {a : Real} (ha : 0 < a) :
    MemLp (zetaFirstApproximationCellTest t a) 2
      AddCircle.haarAddCircle := by
  have hamp : ContinuousOn zetaFirstApproximationTailAmplitude (Ioc a (a + 1)) := by
    exact continuousOn_id.rpow_const fun u hu =>
      Or.inl (ne_of_gt (ha.trans hu.1))
  have hampC : AEStronglyMeasurable
      (fun u : Real => (zetaFirstApproximationTailAmplitude u : Complex))
      (volume.restrict (Ioc a (a + 1))) :=
    (Complex.continuous_ofReal.comp_continuousOn hamp).aestronglyMeasurable
      measurableSet_Ioc
  have hcell : MemLp
      (fun u : Real =>
        conj ((zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationTailTwist t u))
      2 (volume.restrict (Ioc a (a + 1))) := by
    refine MemLp.of_bound
      ((hampC.mul
        (measurable_zetaFirstApproximationTailTwist t).aestronglyMeasurable).star)
      (a ^ (-3 / 2 : Real)) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    rw [norm_conj, norm_mul, norm_zetaFirstApproximationTailTwist, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      zetaFirstApproximationTailAmplitude,
      abs_of_pos (Real.rpow_pos_of_pos (ha.trans hu.1) (-3 / 2 : Real))]
    exact Real.rpow_le_rpow_of_nonpos ha hu.1.le (by norm_num)
  simpa only [zetaFirstApproximationCellTest] using
    hcell.memLp_liftIoc.haarAddCircle

/-- The source sawtooth is square-integrable on the unit additive circle. -/
theorem zetaFirstApproximationSawtooth_memLp :
    MemLp zetaFirstApproximationSawtooth 2 AddCircle.haarAddCircle := by
  have hinterval :
      MemLp (fun u : Real => (bernoulliFun 1 u : Complex)) 2
        (volume.restrict (Ioc (0 : Real) 1)) := by
    refine MemLp.of_bound
      (Complex.continuous_ofReal.comp
        (continuous_bernoulliFun 1)).aestronglyMeasurable 1 ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    rw [bernoulliFun_one, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hu.1, hu.2]
  have hinterval' :
      MemLp (fun u : Real => (bernoulliFun 1 u : Complex)) 2
        (volume.restrict (Ioc (0 : Real) (0 + 1))) := by
    simpa using hinterval
  exact hinterval'.memLp_liftIoc.haarAddCircle

/-- The exact nonzero Fourier coefficients of the source sawtooth. -/
theorem fourierCoeff_zetaFirstApproximationSawtooth (n : Int) :
    fourierCoeff zetaFirstApproximationSawtooth n =
      -1 / (2 * Real.pi * Complex.I * (n : Complex)) := by
  rw [zetaFirstApproximationSawtooth, fourierCoeff_liftIoc_eq]
  simpa [bernoulliFourierCoeff] using
    (bernoulliFourierCoeff_eq (k := 1) (by norm_num) n)

/-- The source sawtooth coefficient has the expected inverse-mode norm. -/
theorem norm_fourierCoeff_zetaFirstApproximationSawtooth (n : Int) :
    ‖fourierCoeff zetaFirstApproximationSawtooth n‖ =
      1 / (2 * Real.pi * |(n : Real)|) := by
  rw [fourierCoeff_zetaFirstApproximationSawtooth]
  simp [abs_of_nonneg Real.pi_pos.le]

/-- The full source contribution of one Fourier mode to the normalized tail. -/
def zetaFirstApproximationModeContribution
    (t a : Real) (n : Int) : Complex :=
  fourierCoeff zetaFirstApproximationSawtooth n *
    ∫ u in Set.Ioi a,
      (zetaFirstApproximationTailAmplitude u : Complex) *
        zetaFirstApproximationModeOscillation t n u

/-- Each reconstructed mode is the Fourier monomial paired with the common tail weight. -/
theorem zetaFirstApproximationModeContribution_eq_fourierIntegral
    (t a : Real) (n : Int) :
    zetaFirstApproximationModeContribution t a n =
      fourierCoeff zetaFirstApproximationSawtooth n *
        ∫ u in Ioi a,
          fourier n (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u := by
  rw [zetaFirstApproximationModeContribution]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  rw [zetaFirstApproximationModeOscillation_eq_fourier_mul_tailTwist]
  ring

/--
After inserting the source sawtooth coefficient, the mode bound gains a
summable inverse square, with an even smaller inverse-cube curvature term.
-/
theorem norm_zetaFirstApproximationModeContribution_le
    {T t a : Real} (n : Int) (hn : n ≠ 0) (hT : 0 < T)
    (ht : 0 ≤ t) (ht' : t ≤ 2 * T) (ha : 3 * T / Real.pi ≤ a) :
    ‖zetaFirstApproximationModeContribution t a n‖ ≤
      (3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
          (1 / |(n : Real)| ^ 2) +
        (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
          (1 / |(n : Real)| ^ 3) := by
  have hn_abs : 0 < |(n : Real)| := by
    rw [abs_pos]
    exact_mod_cast hn
  rw [zetaFirstApproximationModeContribution, norm_mul,
    norm_fourierCoeff_zetaFirstApproximationSawtooth]
  calc
    1 / (2 * Real.pi * |(n : Real)|) *
        ‖∫ u in Set.Ioi a,
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeOscillation t n u‖ ≤
      1 / (2 * Real.pi * |(n : Real)|) *
        (2 * a ^ (-3 / 2 : Real) *
            (1 / ((4 * Real.pi / 3) * |(n : Real)|)) +
          ((2 / 5 : Real) * t /
              ((4 * Real.pi / 3) * |(n : Real)|) ^ 2) *
            a ^ (-5 / 2 : Real)) :=
      mul_le_mul_of_nonneg_left
        (norm_integral_Ioi_zetaFirstApproximationMode_le
          n hn hT ht ht' ha)
        (by positivity)
    _ = (3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
          (1 / |(n : Real)| ^ 2) +
        (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
          (1 / |(n : Real)| ^ 3) := by
      field_simp [Real.pi_ne_zero, hn_abs.ne']
      ring

/-- The explicit inverse-square plus inverse-cube contribution majorant is summable. -/
theorem summable_zetaFirstApproximationModeContribution_majorant
    (t a : Real) :
    Summable (fun n : Int =>
      (3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
          (1 / |(n : Real)| ^ 2) +
        (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
          (1 / |(n : Real)| ^ 3)) := by
  have htwo : Summable (fun n : Int => 1 / |(n : Real)| ^ 2) := by
    simpa only [sq_abs] using
      (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hthree : Summable (fun n : Int => 1 / |(n : Real)| ^ 3) := by
    have h := (Real.summable_one_div_int_pow (p := 3)).mpr (by norm_num)
    simpa only [Real.norm_eq_abs, norm_div, norm_one, abs_pow] using h.norm
  exact
    (htwo.mul_left
      ((3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real))).add
    (hthree.mul_left
      ((9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real)))

/-- The source Fourier-mode contributions form an absolutely convergent series. -/
theorem summable_zetaFirstApproximationModeContribution
    {T t a : Real} (hT : 0 < T) (ht : 0 ≤ t) (ht' : t ≤ 2 * T)
    (ha : 3 * T / Real.pi ≤ a) :
    Summable (zetaFirstApproximationModeContribution t a) := by
  refine (summable_zetaFirstApproximationModeContribution_majorant t a).of_norm_bounded ?_
  intro n
  by_cases hn : n = 0
  · subst n
    simp [zetaFirstApproximationModeContribution,
      fourierCoeff_zetaFirstApproximationSawtooth]
  · exact norm_zetaFirstApproximationModeContribution_le n hn hT ht ht' ha

/-- The absolutely convergent Fourier reconstruction of the normalized source tail. -/
def zetaFirstApproximationFourierTail (t a : Real) : Complex :=
  ∑' n : Int, zetaFirstApproximationModeContribution t a n

/-- The reconstructed Fourier tail is bounded by the explicit summable majorant. -/
theorem norm_zetaFirstApproximationFourierTail_le_tsum_majorant
    {T t a : Real} (hT : 0 < T) (ht : 0 ≤ t) (ht' : t ≤ 2 * T)
    (ha : 3 * T / Real.pi ≤ a) :
    ‖zetaFirstApproximationFourierTail t a‖ ≤
      ∑' n : Int,
        ((3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
            (1 / |(n : Real)| ^ 2) +
          (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
            (1 / |(n : Real)| ^ 3)) := by
  have hContribution :=
    summable_zetaFirstApproximationModeContribution hT ht ht' ha
  have hMajorant := summable_zetaFirstApproximationModeContribution_majorant t a
  rw [zetaFirstApproximationFourierTail]
  calc
    ‖∑' n : Int, zetaFirstApproximationModeContribution t a n‖ ≤
        ∑' n : Int, ‖zetaFirstApproximationModeContribution t a n‖ :=
      norm_tsum_le_tsum_norm hContribution.norm
    _ ≤ ∑' n : Int,
        ((3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
            (1 / |(n : Real)| ^ 2) +
          (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
            (1 / |(n : Real)| ^ 3)) := by
      apply hContribution.norm.tsum_le_tsum
      · intro n
        by_cases hn : n = 0
        · subst n
          simp [zetaFirstApproximationModeContribution,
            fourierCoeff_zetaFirstApproximationSawtooth]
        · exact norm_zetaFirstApproximationModeContribution_le n hn hT ht ht' ha
      · exact hMajorant

/--
The source sawtooth is identified by its exact Fourier series in `L²`.
This is the convergence notion needed to pass the sawtooth factor through a
square-integrable test function in the nonresonant tail estimate.
-/
theorem hasSum_fourier_zetaFirstApproximationSawtooth :
    HasSum
      (fun n : Int =>
        (-1 / (2 * Real.pi * Complex.I * (n : Complex))) • fourierLp 2 n)
      (zetaFirstApproximationSawtooth_memLp.toLp
        zetaFirstApproximationSawtooth) := by
  have h := hasSum_fourier_series_L2
    (zetaFirstApproximationSawtooth_memLp.toLp
      zetaFirstApproximationSawtooth)
  rw [fourierCoeff_congr_ae
    zetaFirstApproximationSawtooth_memLp.coeFn_toLp] at h
  simpa only [fourierCoeff_zetaFirstApproximationSawtooth] using h

/--
The source Fourier expansion may be paired termwise with any `L²` test
function.  This is the finite-period limit passage used before the improper
tail limit is taken.
-/
theorem hasSum_inner_fourier_zetaFirstApproximationSawtooth
    (g : Lp Complex 2 AddCircle.haarAddCircle) :
    HasSum
      (fun n : Int =>
        inner Complex g
          ((-1 / (2 * Real.pi * Complex.I * (n : Complex))) •
            fourierLp 2 n))
      (inner Complex g
        (zetaFirstApproximationSawtooth_memLp.toLp
          zetaFirstApproximationSawtooth)) := by
  simpa only [innerSL_apply_apply] using
    hasSum_fourier_zetaFirstApproximationSawtooth.mapL
      (innerSL Complex g)

/--
On one positive unit cell, the exact `L²` Fourier pairing is the concrete
source-weighted sawtooth integral.  This is the local analytic identity whose
adjacent-cell limit reconstructs the improper Euler remainder.
-/
theorem hasSum_zetaFirstApproximation_cellFourierIntegrals
    (t : Real) {a : Real} (ha : 0 < a) :
    HasSum
      (fun n : Int =>
        fourierCoeff zetaFirstApproximationSawtooth n *
          ∫ u in a..a + 1,
            fourier n (u : UnitAddCircle) *
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationTailTwist t u)
      (∫ u in a..a + 1,
        zetaFirstApproximationSawtooth (u : UnitAddCircle) *
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationTailTwist t u) := by
  let hcell := zetaFirstApproximationCellTest_memLp t ha
  let g : Lp Complex 2 AddCircle.haarAddCircle :=
    hcell.toLp (zetaFirstApproximationCellTest t a)
  have hinner_fourier (n : Int) :
      inner Complex g (fourierLp 2 n) =
        ∫ u in a..a + 1,
          fourier n (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u := by
    rw [MeasureTheory.L2.inner_def]
    simp only [RCLike.inner_apply']
    calc
      (∫ x : UnitAddCircle, conj (g x) * (fourierLp 2 n) x
          ∂AddCircle.haarAddCircle) =
          ∫ x : UnitAddCircle,
            conj (zetaFirstApproximationCellTest t a x) * fourier n x
              ∂AddCircle.haarAddCircle := by
            apply integral_congr_ae
            filter_upwards [hcell.coeFn_toLp, coeFn_fourierLp 2 n] with x hxg hxn
            rw [hxg, hxn]
      _ = ∫ x : UnitAddCircle,
            conj (zetaFirstApproximationCellTest t a x) * fourier n x := by
            rw [AddCircle.integral_haarAddCircle]
            simp
      _ = ∫ u in a..a + 1,
            fourier n (u : UnitAddCircle) *
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationTailTwist t u := by
            rw [← AddCircle.intervalIntegral_preimage (T := (1 : Real)) a]
            apply intervalIntegral.integral_congr_ae
            filter_upwards [] with u hu
            rw [uIoc_of_le (by linarith)] at hu
            rw [zetaFirstApproximationCellTest,
              AddCircle.liftIoc_coe_apply hu]
            simp only [map_mul, conj_ofReal, conj_conj]
            ring
  have hinner_sawtooth :
      inner Complex g
          (zetaFirstApproximationSawtooth_memLp.toLp
            zetaFirstApproximationSawtooth) =
        ∫ u in a..a + 1,
          zetaFirstApproximationSawtooth (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u := by
    rw [MeasureTheory.L2.inner_def]
    simp only [RCLike.inner_apply']
    calc
      (∫ x : UnitAddCircle,
          conj (g x) *
            (zetaFirstApproximationSawtooth_memLp.toLp
              zetaFirstApproximationSawtooth) x
          ∂AddCircle.haarAddCircle) =
          ∫ x : UnitAddCircle,
            conj (zetaFirstApproximationCellTest t a x) *
              zetaFirstApproximationSawtooth x
              ∂AddCircle.haarAddCircle := by
            apply integral_congr_ae
            filter_upwards [hcell.coeFn_toLp,
              zetaFirstApproximationSawtooth_memLp.coeFn_toLp] with x hxg hxs
            rw [hxg, hxs]
      _ = ∫ x : UnitAddCircle,
            conj (zetaFirstApproximationCellTest t a x) *
              zetaFirstApproximationSawtooth x := by
            rw [AddCircle.integral_haarAddCircle]
            simp
      _ = ∫ u in a..a + 1,
          zetaFirstApproximationSawtooth (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u := by
            rw [← AddCircle.intervalIntegral_preimage (T := (1 : Real)) a]
            apply intervalIntegral.integral_congr_ae
            filter_upwards [] with u hu
            rw [uIoc_of_le (by linarith)] at hu
            rw [zetaFirstApproximationCellTest,
              AddCircle.liftIoc_coe_apply hu]
            simp only [map_mul, conj_ofReal, conj_conj]
            ring
  have h := hasSum_inner_fourier_zetaFirstApproximationSawtooth g
  rw [hinner_sawtooth] at h
  refine HasSum.congr_fun h (fun n => ?_)
  rw [inner_smul_right, hinner_fourier,
    fourierCoeff_zetaFirstApproximationSawtooth]

/--
Summing the local Fourier identity over finitely many adjacent source cells
gives the exact weighted identity on the whole finite tail block.
-/
theorem hasSum_zetaFirstApproximation_finiteFourierIntegrals
    (t : Real) {a : Real} (ha : 0 < a) (N : Nat) :
    HasSum
      (fun n : Int =>
        fourierCoeff zetaFirstApproximationSawtooth n *
          ∫ u in a..a + N,
            fourier n (u : UnitAddCircle) *
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationTailTwist t u)
      (∫ u in a..a + N,
        zetaFirstApproximationSawtooth (u : UnitAddCircle) *
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationTailTwist t u) := by
  let b : Nat → Real := fun k => a + k
  have hb_pos (k : Nat) : 0 < b k := by
    dsimp [b]
    exact ha.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg k))
  have hb_step (k : Nat) : b k < b (k + 1) := by
    simp [b, Nat.cast_add, Nat.cast_one]
  have hmodeInterval (n : Int) (k : Nat) :
      IntervalIntegrable
        (fun u : Real =>
          fourier n (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u)
        volume (b k) (b (k + 1)) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (hb_step k).le]
    exact (integrableOn_zetaFirstApproximationFourierTailWeight t n ha).mono_set
      (fun u hu => (show a < u by
        exact lt_of_le_of_lt
          (le_add_of_nonneg_right (Nat.cast_nonneg k)) hu.1))
  have hsawAE :
      zetaFirstApproximationSawtoothTailIntegrand t =ᵐ[volume]
        fun u : Real =>
          zetaFirstApproximationSawtooth (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u := by
    filter_upwards [ae_zetaFirstApproximationSawtooth_coe_eq_realSawtooth]
      with u hu
    simp only [zetaFirstApproximationSawtoothTailIntegrand, hu]
  have hsawInterval (k : Nat) :
      IntervalIntegrable
        (fun u : Real =>
          zetaFirstApproximationSawtooth (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u)
        volume (b k) (b (k + 1)) := by
    have hreal : IntervalIntegrable
        (zetaFirstApproximationSawtoothTailIntegrand t)
        volume (b k) (b (k + 1)) := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (hb_step k).le]
      exact (integrableOn_zetaFirstApproximationSawtoothTailIntegrand t ha).mono_set
        (fun u hu => (show a < u by
          exact lt_of_le_of_lt
            (le_add_of_nonneg_right (Nat.cast_nonneg k)) hu.1))
    apply hreal.congr_ae
    exact Eventually.filter_mono (ae_mono Measure.restrict_le_self) hsawAE
  have hcell (k : Nat) :
      HasSum
        (fun n : Int =>
          fourierCoeff zetaFirstApproximationSawtooth n *
            ∫ u in b k..b (k + 1),
              fourier n (u : UnitAddCircle) *
                (zetaFirstApproximationTailAmplitude u : Complex) *
                  zetaFirstApproximationTailTwist t u)
        (∫ u in b k..b (k + 1),
          zetaFirstApproximationSawtooth (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u) := by
    simpa [b, Nat.cast_add, Nat.cast_one, add_assoc] using
      hasSum_zetaFirstApproximation_cellFourierIntegrals t (hb_pos k)
  have hsum := hasSum_sum (s := Finset.range N) (fun k _ => hcell k)
  convert hsum using 1
  · funext n
    rw [← Finset.mul_sum]
    congr 1
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hmodeInterval n k)]
    simp [b]
  · rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hsawInterval k)]
    simp [b]

/--
The finite-block Fourier summands satisfy a summable bound independent of the
number of cells.  This is the Tannery majorant needed for the improper limit.
-/
theorem norm_zetaFirstApproximation_finiteFourierContribution_le
    {T t a b : Real} (n : Int) (hT : 0 < T) (ht : 0 ≤ t)
    (ht' : t ≤ 2 * T) (ha : 3 * T / Real.pi ≤ a) (hab : a ≤ b) :
    ‖fourierCoeff zetaFirstApproximationSawtooth n *
        ∫ u in a..b,
          fourier n (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u‖ ≤
      2 * ((3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
            (1 / |(n : Real)| ^ 2) +
          (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
            (1 / |(n : Real)| ^ 3)) := by
  by_cases hn : n = 0
  · subst n
    simp [fourierCoeff_zetaFirstApproximationSawtooth]
  have ha_pos : 0 < a := (by positivity : 0 < 3 * T / Real.pi).trans_le ha
  have hb_cut : 3 * T / Real.pi ≤ b := ha.trans hab
  have hfinitePhase :
      (∫ u in a..b,
        fourier n (u : UnitAddCircle) *
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationTailTwist t u) =
        ∫ u in a..b,
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeOscillation t n u := by
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [zetaFirstApproximationModeOscillation_eq_fourier_mul_tailTwist]
    ring
  have hOriginal :=
    integrableOn_zetaFirstApproximationTailAmplitude_mul_modeOscillation
      (t := t) n ha_pos
  have hsplit :
      (∫ u in a..b,
        (zetaFirstApproximationTailAmplitude u : Complex) *
          zetaFirstApproximationModeOscillation t n u) +
        (∫ u in Ioi b,
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeOscillation t n u) =
        ∫ u in Ioi a,
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationModeOscillation t n u := by
    exact intervalIntegral.integral_interval_add_Ioi hOriginal
      (hOriginal.mono_set (Ioi_subset_Ioi hab))
  have hcontribution :
      fourierCoeff zetaFirstApproximationSawtooth n *
          (∫ u in a..b,
            fourier n (u : UnitAddCircle) *
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationTailTwist t u) =
        zetaFirstApproximationModeContribution t a n -
          zetaFirstApproximationModeContribution t b n := by
    rw [hfinitePhase, zetaFirstApproximationModeContribution,
      zetaFirstApproximationModeContribution]
    rw [eq_sub_iff_add_eq]
    calc
      fourierCoeff zetaFirstApproximationSawtooth n *
            (∫ u in a..b,
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationModeOscillation t n u) +
          fourierCoeff zetaFirstApproximationSawtooth n *
            (∫ u in Ioi b,
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationModeOscillation t n u) =
          fourierCoeff zetaFirstApproximationSawtooth n *
            ((∫ u in a..b,
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationModeOscillation t n u) +
             ∫ u in Ioi b,
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationModeOscillation t n u) := by ring
      _ = _ := by rw [hsplit]
  let M : Real :=
    (3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
        (1 / |(n : Real)| ^ 2) +
      (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
        (1 / |(n : Real)| ^ 3)
  let Mb : Real :=
    (3 / (4 * Real.pi ^ 2) : Real) * b ^ (-3 / 2 : Real) *
        (1 / |(n : Real)| ^ 2) +
      (9 * t / (80 * Real.pi ^ 3) : Real) * b ^ (-5 / 2 : Real) *
        (1 / |(n : Real)| ^ 3)
  have hM : ‖zetaFirstApproximationModeContribution t a n‖ ≤ M := by
    simpa only [M] using
      norm_zetaFirstApproximationModeContribution_le n hn hT ht ht' ha
  have hMb : ‖zetaFirstApproximationModeContribution t b n‖ ≤ Mb := by
    simpa only [Mb] using
      norm_zetaFirstApproximationModeContribution_le n hn hT ht ht' hb_cut
  have hb3 : b ^ (-3 / 2 : Real) ≤ a ^ (-3 / 2 : Real) :=
    Real.rpow_le_rpow_of_nonpos ha_pos hab (by norm_num)
  have hb5 : b ^ (-5 / 2 : Real) ≤ a ^ (-5 / 2 : Real) :=
    Real.rpow_le_rpow_of_nonpos ha_pos hab (by norm_num)
  have hMbM : Mb ≤ M := by
    dsimp [Mb, M]
    gcongr
  rw [hcontribution]
  calc
    ‖zetaFirstApproximationModeContribution t a n -
        zetaFirstApproximationModeContribution t b n‖ ≤
        ‖zetaFirstApproximationModeContribution t a n‖ +
          ‖zetaFirstApproximationModeContribution t b n‖ := norm_sub_le _ _
    _ ≤ M + Mb := add_le_add hM hMb
    _ ≤ 2 * M := by linarith

/--
The reconstructed Fourier tail is exactly the source sawtooth Euler remainder.
The proof takes finite adjacent-cell identities to the improper limit using
the modewise integration-by-parts majorant and Tannery's theorem.
-/
theorem zetaFirstApproximationFourierTail_eq_sawtoothIntegral
    {T t a : Real} (hT : 0 < T) (ht : 0 ≤ t) (ht' : t ≤ 2 * T)
    (ha : 3 * T / Real.pi ≤ a) :
    zetaFirstApproximationFourierTail t a =
      ∫ u in Ioi a, zetaFirstApproximationSawtoothTailIntegrand t u := by
  have ha_pos : 0 < a := (by positivity : 0 < 3 * T / Real.pi).trans_le ha
  let f : Nat → Int → Complex := fun N n =>
    fourierCoeff zetaFirstApproximationSawtooth n *
      ∫ u in a..a + N,
        fourier n (u : UnitAddCircle) *
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationTailTwist t u
  let bound : Int → Real := fun n =>
    2 * ((3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
          (1 / |(n : Real)| ^ 2) +
        (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
          (1 / |(n : Real)| ^ 3))
  have hEnd : Tendsto (fun N : Nat => a + (N : Real)) atTop atTop := by
    simpa [add_comm] using
      (tendsto_atTop_add_const_right atTop a
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun N : Nat => (N : Real)) atTop atTop))
  have hpoint (n : Int) :
      Tendsto (fun N => f N n) atTop
        (𝓝 (zetaFirstApproximationModeContribution t a n)) := by
    have hintegral := intervalIntegral_tendsto_integral_Ioi
      (f := fun u : Real =>
        fourier n (u : UnitAddCircle) *
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationTailTwist t u)
      a (integrableOn_zetaFirstApproximationFourierTailWeight t n ha_pos) hEnd
    rw [zetaFirstApproximationModeContribution_eq_fourierIntegral]
    exact tendsto_const_nhds.mul hintegral
  have hboundSummable : Summable bound := by
    dsimp [bound]
    exact (summable_zetaFirstApproximationModeContribution_majorant t a).mul_left 2
  have hbound : ∀ᶠ N : Nat in atTop, ∀ n : Int, ‖f N n‖ ≤ bound n := by
    exact Eventually.of_forall fun N n =>
      norm_zetaFirstApproximation_finiteFourierContribution_le
        n hT ht ht' ha (le_add_of_nonneg_right (Nat.cast_nonneg N))
  have hTannery :
      Tendsto (fun N => ∑' n : Int, f N n) atTop
        (𝓝 (zetaFirstApproximationFourierTail t a)) := by
    simpa only [zetaFirstApproximationFourierTail] using
      tendsto_tsum_of_dominated_convergence hboundSummable hpoint hbound
  have hsawAE :
      zetaFirstApproximationSawtoothTailIntegrand t
        =ᵐ[volume.restrict (Ioi a)]
        fun u : Real =>
          zetaFirstApproximationSawtooth (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u := by
    have hae :
        (fun u : Real => zetaFirstApproximationSawtooth (u : UnitAddCircle))
          =ᵐ[volume.restrict (Ioi a)] zetaFirstApproximationRealSawtooth :=
      Eventually.filter_mono
        (ae_mono Measure.restrict_le_self)
        ae_zetaFirstApproximationSawtooth_coe_eq_realSawtooth
    filter_upwards [hae] with u hu
    simp only [zetaFirstApproximationSawtoothTailIntegrand, hu]
  have hsawIntegrable : IntegrableOn
      (fun u : Real =>
        zetaFirstApproximationSawtooth (u : UnitAddCircle) *
          (zetaFirstApproximationTailAmplitude u : Complex) *
            zetaFirstApproximationTailTwist t u)
      (Ioi a) :=
    (integrableOn_zetaFirstApproximationSawtoothTailIntegrand t ha_pos).congr
      hsawAE
  have hsawLimit :
      Tendsto
        (fun N : Nat =>
          ∫ u in a..a + N,
            zetaFirstApproximationSawtooth (u : UnitAddCircle) *
              (zetaFirstApproximationTailAmplitude u : Complex) *
                zetaFirstApproximationTailTwist t u)
        atTop
        (𝓝 (∫ u in Ioi a,
          zetaFirstApproximationSawtoothTailIntegrand t u)) := by
    have h := intervalIntegral_tendsto_integral_Ioi a hsawIntegrable hEnd
    rw [integral_Ioi_zetaFirstApproximationSawtooth_coe_eq_realSawtooth]
      at h
    exact h
  have hfinite : ∀ N : Nat,
      (∑' n : Int, f N n) =
        ∫ u in a..a + N,
          zetaFirstApproximationSawtooth (u : UnitAddCircle) *
            (zetaFirstApproximationTailAmplitude u : Complex) *
              zetaFirstApproximationTailTwist t u := by
    intro N
    exact (hasSum_zetaFirstApproximation_finiteFourierIntegrals
      t ha_pos N).tsum_eq
  exact tendsto_nhds_unique
    (hTannery.congr' (Eventually.of_forall hfinite)) hsawLimit

/-- The actual sawtooth Euler remainder inherits the summable source majorant. -/
theorem norm_integral_Ioi_zetaFirstApproximationSawtoothTailIntegrand_le
    {T t a : Real} (hT : 0 < T) (ht : 0 ≤ t) (ht' : t ≤ 2 * T)
    (ha : 3 * T / Real.pi ≤ a) :
    ‖∫ u in Ioi a, zetaFirstApproximationSawtoothTailIntegrand t u‖ ≤
      ∑' n : Int,
        ((3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
            (1 / |(n : Real)| ^ 2) +
          (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
            (1 / |(n : Real)| ^ 3)) := by
  rw [← zetaFirstApproximationFourierTail_eq_sawtoothIntegral hT ht ht' ha]
  exact norm_zetaFirstApproximationFourierTail_le_tsum_majorant hT ht ht' ha

/-- The source tail majorant separated into its two fixed convergent mode sums. -/
theorem norm_integral_Ioi_zetaFirstApproximationSawtoothTailIntegrand_le_separated
    {T t a : Real} (hT : 0 < T) (ht : 0 ≤ t) (ht' : t ≤ 2 * T)
    (ha : 3 * T / Real.pi ≤ a) :
    ‖∫ u in Ioi a, zetaFirstApproximationSawtoothTailIntegrand t u‖ ≤
      (3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) *
          (∑' n : Int, 1 / |(n : Real)| ^ 2) +
        (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) *
          (∑' n : Int, 1 / |(n : Real)| ^ 3) := by
  have htwo : Summable (fun n : Int => 1 / |(n : Real)| ^ 2) := by
    simpa only [sq_abs] using
      (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hthree : Summable (fun n : Int => 1 / |(n : Real)| ^ 3) := by
    have h := (Real.summable_one_div_int_pow (p := 3)).mpr (by norm_num)
    simpa only [Real.norm_eq_abs, norm_div, norm_one, abs_pow] using h.norm
  refine (norm_integral_Ioi_zetaFirstApproximationSawtoothTailIntegrand_le
    hT ht ht' ha).trans_eq ?_
  rw [(htwo.mul_left
      ((3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real))).tsum_add
    (hthree.mul_left
      ((9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real))),
    tsum_mul_left, tsum_mul_left]

/-- Abel summation gives the zeta Dirichlet series as the integral of its counting function. -/
theorem riemannZeta_eq_mul_integral_natFloor_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    riemannZeta s =
      s * ∫ u in Ioi (1 : Real),
        ((⌊u⌋₊ : Real) : Complex) * (u : Complex) ^ (-(s + 1)) := by
  have hO :
      (fun n : Nat => ∑ k ∈ Finset.Icc 1 n, (1 : Real))
          =O[Filter.atTop] fun n : Nat => (n : Real) ^ (1 : Real) := by
    simpa [Real.rpow_one] using
      (Asymptotics.isBigO_refl (fun n : Nat => (n : Real)) Filter.atTop)
  have hL := LSeries_eq_mul_integral_of_nonneg
    (fun _ : Nat => (1 : Real)) (r := (1 : Real)) zero_le_one hs hO (fun _ => zero_le_one)
  have hseries : LSeries (fun _ : Nat => (1 : Complex)) s = riemannZeta s := by
    rw [LSeries, zeta_eq_tsum_one_div_nat_cpow hs]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term, Complex.zero_cpow (ne_zero_of_one_lt_re hs)]
    · simp [LSeries.term, hn]
  rw [← hseries]
  simpa using hL

/-- On the convergent half-plane, the counting-function integral splits off the centered sawtooth. -/
theorem riemannZeta_eq_mul_integral_centeredSawtooth_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    riemannZeta s =
      s * ∫ u in Ioi (1 : Real),
        ((u : Complex) - zetaFirstApproximationRealSawtooth u - (1 / 2 : Real)) *
          (u : Complex) ^ (-(s + 1)) := by
  rw [riemannZeta_eq_mul_integral_natFloor_of_one_lt_re hs]
  apply congrArg (fun z : Complex => s * z)
  refine integral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  have hu_nonneg : 0 ≤ u := (zero_lt_one.trans hu).le
  rw [natCast_floor_eq_intCast_floor hu_nonneg]
  have hfloor : ((⌊u⌋ : Int) : Real) = u - Int.fract u := by
    linarith [Int.floor_add_fract u]
  rw [show ((((⌊u⌋ : Int) : Real)) : Complex) =
      (u : Complex) - zetaFirstApproximationRealSawtooth u - (1 / 2 : Real) by
    rw [zetaFirstApproximationRealSawtooth, bernoulliFun_one]
    push_cast [hfloor]
    ring]

/-- The Euler-summation formula with its centered first-Bernoulli remainder on `re s > 1`. -/
theorem riemannZeta_eq_eulerSawtooth_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    riemannZeta s =
      1 / (s - 1) + 1 / 2 -
        s * ∫ u in Ioi (1 : Real),
          zetaFirstApproximationRealSawtooth u *
            (u : Complex) ^ (-(s + 1)) := by
  have hs_pos : 0 < s.re := zero_lt_one.trans hs
  have hs_ne : s ≠ 0 := ne_zero_of_re_pos hs_pos
  have hs_one_ne : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_apply_ne re (by simp [hs.ne']))
  have hq : IntegrableOn
      (fun u : Real => (u : Complex) ^ (-(s + 1))) (Ioi (1 : Real)) := by
    exact integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hsaw : IntegrableOn
      (fun u : Real => zetaFirstApproximationRealSawtooth u *
        (u : Complex) ^ (-(s + 1))) (Ioi (1 : Real)) :=
    integrableOn_zetaFirstApproximationRealSawtooth_mul_cpow hs_pos zero_lt_one
  have hmul_ae :
      (fun u : Real => (u : Complex) * (u : Complex) ^ (-(s + 1)))
        =ᵐ[volume.restrict (Ioi (1 : Real))]
      (fun u : Real => (u : Complex) ^ (-s)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have huC : (u : Complex) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hu).ne'
    calc
      (u : Complex) * (u : Complex) ^ (-(s + 1)) =
          (u : Complex) ^ (1 : Complex) * (u : Complex) ^ (-(s + 1)) := by simp
      _ = (u : Complex) ^ ((1 : Complex) + -(s + 1)) :=
        (Complex.cpow_add _ _ huC).symm
      _ = (u : Complex) ^ (-s) := by congr 1; ring
  have hmul : IntegrableOn
      (fun u : Real => (u : Complex) * (u : Complex) ^ (-(s + 1)))
      (Ioi (1 : Real)) := by
    exact (integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one).congr hmul_ae.symm
  have hq_value :
      (∫ u in Ioi (1 : Real), (u : Complex) ^ (-(s + 1))) = 1 / s := by
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
    norm_num only [Complex.ofReal_one, Complex.one_cpow]
    field_simp [hs_ne]
    ring
  have hmul_value :
      (∫ u in Ioi (1 : Real),
        (u : Complex) * (u : Complex) ^ (-(s + 1))) = 1 / (s - 1) := by
    rw [integral_congr_ae hmul_ae,
      integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
    norm_num only [Complex.ofReal_one, Complex.one_cpow]
    rw [show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
  have hsplit :
      (∫ u in Ioi (1 : Real),
        ((u : Complex) - zetaFirstApproximationRealSawtooth u - (1 / 2 : Real)) *
          (u : Complex) ^ (-(s + 1))) =
        (∫ u in Ioi (1 : Real),
          (u : Complex) * (u : Complex) ^ (-(s + 1))) -
        (∫ u in Ioi (1 : Real),
          zetaFirstApproximationRealSawtooth u *
            (u : Complex) ^ (-(s + 1))) -
        (1 / 2 : Complex) *
          ∫ u in Ioi (1 : Real), (u : Complex) ^ (-(s + 1)) := by
    calc
      _ = ∫ u in Ioi (1 : Real),
          ((u : Complex) * (u : Complex) ^ (-(s + 1)) -
            zetaFirstApproximationRealSawtooth u *
              (u : Complex) ^ (-(s + 1))) -
            (1 / 2 : Complex) * (u : Complex) ^ (-(s + 1)) := by
          refine integral_congr_ae ?_
          filter_upwards with u
          push_cast
          ring
      _ = _ := by
        have houter := integral_sub (μ := volume.restrict (Ioi (1 : Real)))
          (hmul.sub hsaw) (hq.const_mul (1 / 2 : Complex))
        have hinner := integral_sub (μ := volume.restrict (Ioi (1 : Real))) hmul hsaw
        simpa only [Pi.sub_apply, integral_const_mul] using houter.trans
          (congrArg (fun z : Complex => z -
            ∫ u in Ioi (1 : Real),
              (1 / 2 : Complex) * (u : Complex) ^ (-(s + 1))) hinner)
  rw [riemannZeta_eq_mul_integral_centeredSawtooth_of_one_lt_re hs,
    hsplit, hmul_value, hq_value]
  field_simp [hs_ne, hs_one_ne]
  ring

/-- Analytic continuation of the Euler-sawtooth formula to the positive upper quadrant. -/
theorem riemannZeta_eq_eulerSawtooth_of_re_pos_of_im_pos
    {s : Complex} (hs_re : 0 < s.re) (hs_im : 0 < s.im) :
    riemannZeta s =
      1 / (s - 1) + 1 / 2 -
        s * ∫ u in Ioi (1 : Real),
          zetaFirstApproximationRealSawtooth u *
            (u : Complex) ^ (-(s + 1)) := by
  let U : Set Complex := {z | 0 < z.re ∧ 0 < z.im}
  let G : Complex → Complex := fun z =>
    1 / (z - 1) + 1 / 2 -
      z * ∫ u in Ioi (1 : Real),
        zetaFirstApproximationRealSawtooth u *
          (u : Complex) ^ (-(z + 1))
  have hU_open : IsOpen U := by
    dsimp [U]
    exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_const continuous_im)
  have hU_convex : Convex Real U := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨hx_re, hx_im⟩
    rcases hy with ⟨hy_re, hy_im⟩
    have hw : 0 < a ∨ 0 < b := by
      by_cases ha_pos : 0 < a
      · exact Or.inl ha_pos
      · right
        have ha_zero : a = 0 := le_antisymm (le_of_not_gt ha_pos) ha
        nlinarith
    constructor
    · simp only [add_re, smul_re, smul_eq_mul]
      rcases hw with ha_pos | hb_pos
      · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx_re) (mul_nonneg hb hy_re.le)
      · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx_re.le) (mul_pos hb_pos hy_re)
    · simp only [add_im, smul_im, smul_eq_mul]
      rcases hw with ha_pos | hb_pos
      · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx_im) (mul_nonneg hb hy_im.le)
      · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx_im.le) (mul_pos hb_pos hy_im)
  have hU_preconnected : IsPreconnected U := hU_convex.isPreconnected
  have hzeta : AnalyticOnNhd Complex riemannZeta U :=
    analyticOn_riemannZeta.mono fun z hz => by
      intro h
      subst z
      simpa using hz.2.ne'
  have hG_diff : DifferentiableOn Complex G U := by
    intro z hz
    have hz_one : z - 1 ≠ 0 := by
      intro h
      have : z = 1 := sub_eq_zero.mp h
      subst z
      simpa using hz.2.ne'
    have hIntegral :=
      differentiableAt_zetaFirstApproximationEulerSawtoothIntegral hz.1
    have hOneTerm : DifferentiableAt Complex (fun w : Complex => 1 / (w - 1)) z :=
      (differentiableAt_const (1 : Complex)).div
        (differentiableAt_id.sub_const (1 : Complex)) hz_one
    have hHalf : DifferentiableAt Complex (fun _ : Complex => (1 / 2 : Complex)) z :=
      differentiableAt_const (1 / 2 : Complex)
    have hProd : DifferentiableAt Complex
        (fun w : Complex => w * ∫ u in Ioi (1 : Real),
          zetaFirstApproximationRealSawtooth u *
            (u : Complex) ^ (-(w + 1))) z :=
      differentiableAt_id.mul hIntegral
    exact ((hOneTerm.add hHalf).sub hProd).differentiableWithinAt
  have hG : AnalyticOnNhd Complex G U := hG_diff.analyticOnNhd hU_open
  let z₀ : Complex := 2 + Complex.I
  have hz₀ : z₀ ∈ U := by simp [z₀, U]
  have heq : riemannZeta =ᶠ[𝓝 z₀] G := by
    have hopen : IsOpen {z : Complex | 1 < z.re} :=
      isOpen_lt continuous_const continuous_re
    have hz₀_re : z₀ ∈ {z : Complex | 1 < z.re} := by simp [z₀]
    filter_upwards [hopen.mem_nhds hz₀_re] with z hz
    exact riemannZeta_eq_eulerSawtooth_of_one_lt_re hz
  have hEqOn : Set.EqOn riemannZeta G U :=
    hzeta.eqOn_of_preconnected_of_eventuallyEq hG hU_preconnected hz₀ heq
  simpa only [G] using hEqOn ⟨hs_re, hs_im⟩

/-- The analytically continued Euler identity in the exact critical-line normalization. -/
theorem riemannZeta_criticalLine_eq_eulerSawtooth
    {t : Real} (ht : 0 < t) :
    riemannZeta (((1 / 2 : Real) : Complex) + t * Complex.I) =
      1 / ((((1 / 2 : Real) : Complex) + t * Complex.I) - 1) + 1 / 2 -
        (((1 / 2 : Real) : Complex) + t * Complex.I) *
          ∫ u in Ioi (1 : Real),
            zetaFirstApproximationSawtoothTailIntegrand t u := by
  let s : Complex := ((1 / 2 : Real) : Complex) + t * Complex.I
  have hs_re : 0 < s.re := by simp [s]
  have hs_im : 0 < s.im := by simpa [s] using ht
  have hEuler := riemannZeta_eq_eulerSawtooth_of_re_pos_of_im_pos hs_re hs_im
  have hIntegral :
      (∫ u in Ioi (1 : Real),
        zetaFirstApproximationRealSawtooth u *
          (u : Complex) ^ (-(s + 1))) =
      ∫ u in Ioi (1 : Real),
        zetaFirstApproximationSawtoothTailIntegrand t u := by
    refine integral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [zetaFirstApproximationSawtoothTailIntegrand_eq_cpow t (zero_lt_one.trans hu)]
    congr 2
    dsimp [s]
    ring
  simpa only [s, hIntegral] using hEuler

/-- Abel summation for a finite complex-power prefix, with the floor term still explicit. -/
theorem sum_Icc_cpow_eq_floorIntegral
    {s : Complex} (hs : s ≠ 0) (m : Nat) :
    ∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s) =
      (m : Complex) ^ (-s) * m -
        ∫ u in Set.Ioc (1 : Real) m,
          ((-s) * (u : Complex) ^ (-s - 1)) * (⌊u⌋₊ : Nat) := by
  let f : Real → Complex := fun u => (u : Complex) ^ (-s)
  let c : Nat → Complex := fun n => if n = 0 then 0 else 1
  have hf_diff : ∀ u ∈ Set.Icc (1 : Real) m, DifferentiableAt Real f u := by
    intro u hu
    change DifferentiableAt Real (fun y : Real => (y : Complex) ^ (-s)) u
    exact (hasDerivAt_ofReal_cpow_const
      (zero_lt_one.trans_le hu.1).ne' (neg_ne_zero.mpr hs)).differentiableAt
  have hderiv {u : Real} (hu : 0 < u) :
      deriv f u = (-s) * (u : Complex) ^ (-s - 1) := by
    change deriv (fun y : Real => (y : Complex) ^ (-s)) u = _
    rw [Complex.deriv_ofReal_cpow_const hu.ne' (neg_ne_zero.mpr hs)]
  have hf_int : IntegrableOn (deriv f) (Set.Icc (1 : Real) m) := by
    by_cases hm : m = 0
    · subst m
      rw [Set.Icc_eq_empty_of_lt (by norm_num)]
      exact integrableOn_empty
    · have hcont : ContinuousOn
          (fun u : Real => (-s) * (u : Complex) ^ (-s - 1))
          (Set.Icc (1 : Real) m) := by
        exact continuousOn_const.mul fun u hu =>
          (continuousAt_ofReal_cpow_const _ _
            (Or.inr (zero_lt_one.trans_le hu.1).ne')).continuousWithinAt
      refine (hcont.integrableOn_Icc).congr ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
      rw [hderiv (zero_lt_one.trans_le hu.1)]
  have hAbel := sum_mul_eq_sub_integral_mul₀'
    (f := f) (c := c) (by simp [c]) m hf_diff hf_int
  have hc_sum (n : Nat) :
      ∑ k ∈ Finset.Icc 0 n, c k = (n : Complex) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons]
    simp only [c, if_pos, zero_add]
    calc
      (∑ x ∈ Finset.Ioc 0 n, if x = 0 then 0 else 1) =
          ∑ _x ∈ Finset.Ioc 0 n, (1 : Complex) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [if_neg (Nat.ne_of_gt (Finset.mem_Ioc.mp hk).1)]
      _ = (n : Complex) := by simp
  have hfc_sum :
      ∑ k ∈ Finset.Icc 0 m, f k * c k =
        ∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons]
    simp only [f, c, if_pos, mul_zero, zero_add]
    have hIoc : Finset.Ioc 0 m = Finset.Icc 1 m := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hIoc]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      have hk1 := (Finset.mem_Icc.mp hk).1
      omega
    rw [if_neg hk0, mul_one]
    norm_cast
  rw [hfc_sum, hc_sum] at hAbel
  simp_rw [hc_sum] at hAbel
  refine hAbel.trans ?_
  congr 1
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
  rw [hderiv (zero_lt_one.trans hu.1)]

/-- The natural floor is the affine term minus the centered first-Bernoulli sawtooth. -/
theorem natFloor_cast_eq_sub_realSawtooth
    {u : Real} (hu : 0 ≤ u) :
    ((⌊u⌋₊ : Nat) : Complex) =
      (u : Complex) - zetaFirstApproximationRealSawtooth u - (1 / 2 : Real) := by
  rw [← ofReal_natCast, natCast_floor_eq_intCast_floor hu]
  have hfloor : ((⌊u⌋ : Int) : Real) = u - Int.fract u := by
    linarith [Int.floor_add_fract u]
  rw [zetaFirstApproximationRealSawtooth, bernoulliFun_one]
  push_cast [hfloor]
  ring

/-- Finite Euler summation at an integer endpoint, with the centered sawtooth remainder explicit. -/
theorem sum_Icc_cpow_eq_eulerSawtooth
    {s : Complex} (hs_re : 0 < s.re) (hs_one : s ≠ 1)
    {a : Nat} (ha : 1 ≤ a) :
    ∑ k ∈ Finset.Icc 1 a, (k : Complex) ^ (-s) =
      1 / (s - 1) + 1 / 2 -
        (a : Complex) ^ (1 - s) / (s - 1) +
        (1 / 2 : Complex) * (a : Complex) ^ (-s) -
        s * ∫ u in Set.Ioc (1 : Real) a,
          zetaFirstApproximationRealSawtooth u *
            (u : Complex) ^ (-(s + 1)) := by
  have hs_zero : s ≠ 0 := ne_zero_of_re_pos hs_re
  have haR : (1 : Real) ≤ a := by exact_mod_cast ha
  have ha_pos : (0 : Real) < a := zero_lt_one.trans_le haR
  let p : Real → Complex := fun u => (u : Complex) ^ (-s)
  let q : Real → Complex := fun u => (u : Complex) ^ (-(s + 1))
  let r : Real → Complex := fun u =>
    zetaFirstApproximationRealSawtooth u * q u
  have hp : IntegrableOn p (Set.Ioc (1 : Real) a) := by
    apply (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro u hu
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le hu.1).ne')).continuousWithinAt
  have hq : IntegrableOn q (Set.Ioc (1 : Real) a) := by
    apply (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro u hu
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le hu.1).ne')).continuousWithinAt
  have hr : IntegrableOn r (Set.Ioc (1 : Real) a) := by
    exact (integrableOn_zetaFirstApproximationRealSawtooth_mul_cpow
      hs_re zero_lt_one).mono_set fun u hu => hu.1
  have hp_value :
      (∫ u in Set.Ioc (1 : Real) a, p u) =
        ((a : Complex) ^ (1 - s) - 1) / (1 - s) := by
    rw [← intervalIntegral.integral_of_le haR]
    rw [show p = fun u : Real => (u : Complex) ^ (-s) by rfl,
      integral_cpow]
    · rw [show (((a : Real) : Complex)) = (a : Complex) by norm_cast]
      norm_num only [Complex.ofReal_one, Complex.one_cpow]
      congr 2 <;> ring_nf
    · right
      constructor
      · intro h
        apply hs_one
        linear_combination -h
      · rw [uIcc_of_le haR]
        simp
  have hq_value :
      (∫ u in Set.Ioc (1 : Real) a, q u) =
        ((a : Complex) ^ (-s) - 1) / (-s) := by
    rw [← intervalIntegral.integral_of_le haR]
    rw [show q = fun u : Real => (u : Complex) ^ (-(s + 1)) by rfl,
      integral_cpow]
    · rw [show (((a : Real) : Complex)) = (a : Complex) by norm_cast]
      norm_num only [Complex.ofReal_one, Complex.one_cpow]
      congr 2 <;> ring_nf
    · right
      constructor
      · intro h
        apply hs_zero
        linear_combination -h
      · rw [uIcc_of_le haR]
        simp
  have hfloor_ae :
      (fun u : Real => ((-s) * q u) * (⌊u⌋₊ : Nat)) =ᵐ[
          volume.restrict (Set.Ioc (1 : Real) a)]
        (fun u => (-s) * p u + s * r u + (s / 2) * q u) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    have hu_pos : 0 < u := zero_lt_one.trans hu.1
    have huC : (u : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have huq : (u : Complex) * q u = p u := by
      calc
        (u : Complex) * q u =
            (u : Complex) ^ (1 : Complex) * (u : Complex) ^ (-(s + 1)) := by
              simp [q]
        _ = (u : Complex) ^ ((1 : Complex) + -(s + 1)) :=
          (Complex.cpow_add _ _ huC).symm
        _ = p u := by change (u : Complex) ^ _ = (u : Complex) ^ (-s); congr 1; ring
    rw [natFloor_cast_eq_sub_realSawtooth hu_pos.le]
    change ((-s) * q u) *
        ((u : Complex) - zetaFirstApproximationRealSawtooth u - (1 / 2 : Real)) = _
    calc
      ((-s) * q u) *
          ((u : Complex) - zetaFirstApproximationRealSawtooth u - (1 / 2 : Real)) =
          (-s) * ((u : Complex) * q u) +
            s * (zetaFirstApproximationRealSawtooth u * q u) +
            (s / 2) * q u := by push_cast; ring
      _ = (-s) * p u + s * r u + (s / 2) * q u := by rw [huq]
  have hintegral :
      (∫ u in Set.Ioc (1 : Real) a,
        ((-s) * q u) * (⌊u⌋₊ : Nat)) =
        (-s) * (∫ u in Set.Ioc (1 : Real) a, p u) +
        s * (∫ u in Set.Ioc (1 : Real) a, r u) +
        (s / 2) * (∫ u in Set.Ioc (1 : Real) a, q u) := by
    rw [integral_congr_ae hfloor_ae]
    calc
      (∫ u in Set.Ioc (1 : Real) a,
          ((-s) * p u + s * r u) + (s / 2) * q u) =
          (∫ u in Set.Ioc (1 : Real) a, (-s) * p u + s * r u) +
            (∫ u in Set.Ioc (1 : Real) a, (s / 2) * q u) :=
        integral_add ((hp.const_mul (-s)).add (hr.const_mul s))
          (hq.const_mul (s / 2))
      _ = ((∫ u in Set.Ioc (1 : Real) a, (-s) * p u) +
            (∫ u in Set.Ioc (1 : Real) a, s * r u)) +
            (∫ u in Set.Ioc (1 : Real) a, (s / 2) * q u) := by
        rw [integral_add (hp.const_mul (-s)) (hr.const_mul s)]
      _ = _ := by simp only [integral_const_mul]
  have hendpoint :
      (a : Complex) ^ (-s) * a = (a : Complex) ^ (1 - s) := by
    calc
      (a : Complex) ^ (-s) * a =
          (a : Complex) ^ (-s) * (a : Complex) ^ (1 : Complex) := by simp
      _ = (a : Complex) ^ (-s + 1) :=
        (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha_pos.ne')).symm
      _ = (a : Complex) ^ (1 - s) := by congr 1; ring
  rw [sum_Icc_cpow_eq_floorIntegral hs_zero a, hendpoint]
  rw [show -s - 1 = -(s + 1) by ring]
  change (a : Complex) ^ (1 - s) -
      ∫ u in Set.Ioc (1 : Real) a, ((-s) * q u) * (⌊u⌋₊ : Nat) = _
  rw [hintegral]
  rw [hp_value, hq_value]
  field_simp [hs_zero, sub_ne_zero.mpr hs_one]
  ring

/-- Finite Euler summation through `m`, with the tail beginning at the successor integer. -/
theorem sum_Icc_cpow_eq_eulerSawtooth_succ
    {s : Complex} (hs_re : 0 < s.re) (hs_one : s ≠ 1) (m : Nat) :
    ∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s) =
      1 / (s - 1) + 1 / 2 -
        ((m + 1 : Nat) : Complex) ^ (1 - s) / (s - 1) -
        (1 / 2 : Complex) * ((m + 1 : Nat) : Complex) ^ (-s) -
        s * ∫ u in Set.Ioc (1 : Real) (m + 1 : Nat),
          zetaFirstApproximationRealSawtooth u *
            (u : Complex) ^ (-(s + 1)) := by
  let a : Nat := m + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hnot : a ∉ Finset.Icc 1 m := by
    simp only [Finset.mem_Icc, not_and_or]
    right
    dsimp [a]
    omega
  have hset : insert a (Finset.Icc 1 m) = Finset.Icc 1 a := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc]
    dsimp [a]
    omega
  have hsum :
      ∑ k ∈ Finset.Icc 1 a, (k : Complex) ^ (-s) =
        (a : Complex) ^ (-s) +
          ∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s) := by
    rw [← hset, Finset.sum_insert hnot]
  have hEuler := sum_Icc_cpow_eq_eulerSawtooth hs_re hs_one ha
  rw [hsum] at hEuler
  dsimp only [a] at hEuler ⊢
  linear_combination hEuler

/-- The analytically continued Euler identity split at the successor of a finite prefix. -/
theorem riemannZeta_eq_sum_Icc_add_eulerSawtoothTail_succ
    {s : Complex} (hs_re : 0 < s.re) (hs_im : 0 < s.im) (m : Nat) :
    riemannZeta s =
      (∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s)) +
        ((m + 1 : Nat) : Complex) ^ (1 - s) / (s - 1) +
        (1 / 2 : Complex) * ((m + 1 : Nat) : Complex) ^ (-s) -
        s * ∫ u in Set.Ioi (((m + 1 : Nat) : Real)),
          zetaFirstApproximationRealSawtooth u *
            (u : Complex) ^ (-(s + 1)) := by
  let a : Real := (m + 1 : Nat)
  let g : Real → Complex := fun u =>
    zetaFirstApproximationRealSawtooth u * (u : Complex) ^ (-(s + 1))
  have hs_one : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.one_im] at him
    linarith
  have ha : (1 : Real) ≤ a := by dsimp [a]; exact_mod_cast Nat.succ_pos m
  have hall : IntegrableOn g (Set.Ioi (1 : Real)) := by
    exact integrableOn_zetaFirstApproximationRealSawtooth_mul_cpow hs_re zero_lt_one
  have hleft : IntegrableOn g (Set.Ioc (1 : Real) a) :=
    hall.mono_set Set.Ioc_subset_Ioi_self
  have hright : IntegrableOn g (Set.Ioi a) := by
    apply hall.mono_set
    exact Set.Ioi_subset_Ioi ha
  have hsplit :
      (∫ u in Set.Ioi (1 : Real), g u) =
        (∫ u in Set.Ioc (1 : Real) a, g u) +
          ∫ u in Set.Ioi a, g u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hleft hright]
  have hZeta := riemannZeta_eq_eulerSawtooth_of_re_pos_of_im_pos hs_re hs_im
  have hfinite := sum_Icc_cpow_eq_eulerSawtooth_succ hs_re hs_one m
  change riemannZeta s = 1 / (s - 1) + 1 / 2 -
      s * (∫ u in Set.Ioi (1 : Real), g u) at hZeta
  change (∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s)) =
      1 / (s - 1) + 1 / 2 -
        ((m + 1 : Nat) : Complex) ^ (1 - s) / (s - 1) -
        (1 / 2 : Complex) * ((m + 1 : Nat) : Complex) ^ (-s) -
        s * (∫ u in Set.Ioc (1 : Real) a, g u) at hfinite
  change riemannZeta s =
      (∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s)) +
        ((m + 1 : Nat) : Complex) ^ (1 - s) / (s - 1) +
        (1 / 2 : Complex) * ((m + 1 : Nat) : Complex) ^ (-s) -
        s * (∫ u in Set.Ioi a, g u)
  rw [hsplit] at hZeta
  linear_combination hZeta - hfinite

/-- Exact critical-line Euler transport to the project's floored cutoff. -/
theorem riemannZeta_criticalLine_eq_cutoffSum_add_sawtoothTail
    {T t : Real} (ht : 0 < t) :
    let s : Complex := ((1 / 2 : Real) : Complex) + t * Complex.I
    let m : Nat := zetaFirstApproximationCutoff T
    let a : Real := (m : Real) + 1
    riemannZeta s =
      (∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s)) +
        (a : Complex) ^ (1 - s) / (s - 1) +
        (1 / 2 : Complex) * (a : Complex) ^ (-s) -
        s * ∫ u in Set.Ioi a,
          zetaFirstApproximationSawtoothTailIntegrand t u := by
  let s : Complex := ((1 / 2 : Real) : Complex) + t * Complex.I
  let m : Nat := zetaFirstApproximationCutoff T
  let a : Real := (m : Real) + 1
  have hs_re : 0 < s.re := by dsimp [s]; norm_num
  have hs_im : 0 < s.im := by simpa [s] using ht
  have hEuler := riemannZeta_eq_sum_Icc_add_eulerSawtoothTail_succ hs_re hs_im m
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have hIntegral :
      (∫ u in Set.Ioi a,
        zetaFirstApproximationRealSawtooth u *
          (u : Complex) ^ (-(s + 1))) =
      ∫ u in Set.Ioi a,
        zetaFirstApproximationSawtoothTailIntegrand t u := by
    refine integral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [zetaFirstApproximationSawtoothTailIntegrand_eq_cpow t (ha_pos.trans hu)]
    congr 2
    dsimp [s]
    ring
  change riemannZeta s =
      (∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s)) +
        (a : Complex) ^ (1 - s) / (s - 1) +
        (1 / 2 : Complex) * (a : Complex) ^ (-s) -
        s * ∫ u in Set.Ioi a,
          zetaFirstApproximationSawtoothTailIntegrand t u
  rw [← hIntegral]
  have haC : (a : Complex) = ((m + 1 : Nat) : Complex) := by
    dsimp [a]
    norm_cast
  rw [haC]
  simpa only [a, Nat.cast_add, Nat.cast_one] using hEuler

/-- The successor pole term is controlled by its elementary critical-line norm. -/
theorem norm_zetaFirstApproximation_successorPole_le
    {t a : Real} (ht : 0 < t) (ha : 0 < a) :
    ‖(a : Complex) ^
          (1 - (((1 / 2 : Real) : Complex) + t * Complex.I)) /
        (((1 / 2 : Real) : Complex) + t * Complex.I - 1)‖ ≤
      Real.sqrt a / t := by
  let s : Complex := ((1 / 2 : Real) : Complex) + t * Complex.I
  have hnum : ‖(a : Complex) ^ (1 - s)‖ = Real.sqrt a := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
    norm_num [s]
    exact (Real.sqrt_eq_rpow a).symm
  have hden : t ≤ ‖s - 1‖ := by
    have him := Complex.abs_im_le_norm (s - 1)
    simpa [s, abs_of_pos ht] using him
  change ‖(a : Complex) ^ (1 - s) / (s - 1)‖ ≤ _
  rw [norm_div, hnum]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg a) ht hden

/-- At the exact floored cutoff, the successor pole costs at most `2 / sqrt T`. -/
theorem norm_zetaFirstApproximation_cutoffSuccessorPole_le
    {T t : Real} (hT : 4 ≤ T) (ht : T ≤ t) :
    let a : Real := (zetaFirstApproximationCutoff T : Real) + 1
    ‖(a : Complex) ^
          (1 - (((1 / 2 : Real) : Complex) + t * Complex.I)) /
        (((1 / 2 : Real) : Complex) + t * Complex.I - 1)‖ ≤
      2 / Real.sqrt T := by
  let a : Real := (zetaFirstApproximationCutoff T : Real) + 1
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have ht_pos : 0 < t := hT_pos.trans_le ht
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have hx_le_T : 3 * T / Real.pi ≤ T := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have ha_le : a ≤ 4 * T := by
    have hsucc := zetaFirstApproximationCutoff_succ_le hT_pos
    dsimp [a]
    linarith
  have hsqrt : Real.sqrt a ≤ 2 * Real.sqrt T := by
    calc
      Real.sqrt a ≤ Real.sqrt (4 * T) := Real.sqrt_le_sqrt ha_le
      _ = 2 * Real.sqrt T := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
        rw [show Real.sqrt (4 : Real) = 2 by
          convert Real.sqrt_sq_eq_abs (2 : Real) using 1 <;> norm_num]
  have hpole := norm_zetaFirstApproximation_successorPole_le ht_pos ha_pos
  calc
    _ ≤ Real.sqrt a / t := hpole
    _ ≤ Real.sqrt a / T :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg a) hT_pos ht
    _ ≤ (2 * Real.sqrt T) / T :=
      div_le_div_of_nonneg_right hsqrt hT_pos.le
    _ = 2 / Real.sqrt T := by
      field_simp [Real.sqrt_ne_zero'.mpr hT_pos]
      rw [Real.sq_sqrt hT_pos.le]

/-- The oscillatory Euler tail, including its critical-line factor, is uniformly `O(T⁻¹ᐟ²)`. -/
theorem norm_zetaFirstApproximation_cutoffSawtoothTail_le
    {T t : Real} (hT : 4 ≤ T) (ht : T ≤ t) (ht' : t ≤ 2 * T) :
    let s : Complex := ((1 / 2 : Real) : Complex) + t * Complex.I
    let a : Real := (zetaFirstApproximationCutoff T : Real) + 1
    let c : Real := 3 / Real.pi
    let S₂ : Real := ∑' n : Int, 1 / |(n : Real)| ^ 2
    let S₃ : Real := ∑' n : Int, 1 / |(n : Real)| ^ 3
    let K : Real :=
      3 * (3 / (4 * Real.pi ^ 2)) * c ^ (-3 / 2 : Real) * S₂ +
        6 * (9 / (80 * Real.pi ^ 3)) * c ^ (-5 / 2 : Real) * S₃
    ‖s * ∫ u in Set.Ioi a,
        zetaFirstApproximationSawtoothTailIntegrand t u‖ ≤
      K / Real.sqrt T := by
  let s : Complex := ((1 / 2 : Real) : Complex) + t * Complex.I
  let a : Real := (zetaFirstApproximationCutoff T : Real) + 1
  let c : Real := 3 / Real.pi
  let S₂ : Real := ∑' n : Int, 1 / |(n : Real)| ^ 2
  let S₃ : Real := ∑' n : Int, 1 / |(n : Real)| ^ 3
  let K : Real :=
    3 * (3 / (4 * Real.pi ^ 2)) * c ^ (-3 / 2 : Real) * S₂ +
      6 * (9 / (80 * Real.pi ^ 3)) * c ^ (-5 / 2 : Real) * S₃
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have ht_nonneg : 0 ≤ t := hT_pos.le.trans ht
  have hx_pos : 0 < 3 * T / Real.pi := by positivity
  have ha : 3 * T / Real.pi ≤ a := by
    exact (zetaFirstApproximationCutoff_lt_succ hT_pos).le
  have ha_pos : 0 < a := hx_pos.trans_le ha
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hS₂ : 0 ≤ S₂ := tsum_nonneg fun n => by positivity
  have hS₃ : 0 ≤ S₃ := tsum_nonneg fun n => by positivity
  have hs_norm : ‖s‖ ≤ 3 * T := by
    calc
      ‖s‖ ≤ ‖(((1 / 2 : Real) : Complex))‖ + ‖t * Complex.I‖ := norm_add_le _ _
      _ = 1 / 2 + t := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num), norm_mul,
          Complex.norm_real, Real.norm_of_nonneg ht_nonneg, norm_I, mul_one]
      _ ≤ 3 * T := by linarith
  have htail :=
    norm_integral_Ioi_zetaFirstApproximationSawtoothTailIntegrand_le_separated
      hT_pos ht_nonneg ht' ha
  have hpow3 : a ^ (-3 / 2 : Real) ≤
      (3 * T / Real.pi) ^ (-3 / 2 : Real) :=
    Real.rpow_le_rpow_of_nonpos hx_pos ha (by norm_num)
  have hpow5 : a ^ (-5 / 2 : Real) ≤
      (3 * T / Real.pi) ^ (-5 / 2 : Real) :=
    Real.rpow_le_rpow_of_nonpos hx_pos ha (by norm_num)
  have hA : 0 ≤ (3 / (4 * Real.pi ^ 2) : Real) := by positivity
  have hBt : 0 ≤ (9 * t / (80 * Real.pi ^ 3) : Real) := by positivity
  have hB2 : 0 ≤ (9 * (2 * T) / (80 * Real.pi ^ 3) : Real) := by positivity
  have hB_le : (9 * t / (80 * Real.pi ^ 3) : Real) ≤
      9 * (2 * T) / (80 * Real.pi ^ 3) := by gcongr
  have hterm3 :
      (3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) * S₂ ≤
        (3 / (4 * Real.pi ^ 2) : Real) *
          (3 * T / Real.pi) ^ (-3 / 2 : Real) * S₂ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow3 hA) hS₂
  have hterm5 :
      (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) * S₃ ≤
        (9 * (2 * T) / (80 * Real.pi ^ 3) : Real) *
          (3 * T / Real.pi) ^ (-5 / 2 : Real) * S₃ := by
    calc
      _ ≤ (9 * (2 * T) / (80 * Real.pi ^ 3) : Real) *
          a ^ (-5 / 2 : Real) * S₃ := by
        gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow5 hB2) hS₃
  change ‖s * ∫ u in Set.Ioi a,
      zetaFirstApproximationSawtoothTailIntegrand t u‖ ≤ K / Real.sqrt T
  rw [norm_mul]
  calc
    ‖s‖ * ‖∫ u in Set.Ioi a,
        zetaFirstApproximationSawtoothTailIntegrand t u‖ ≤
      (3 * T) *
        ((3 / (4 * Real.pi ^ 2) : Real) * a ^ (-3 / 2 : Real) * S₂ +
          (9 * t / (80 * Real.pi ^ 3) : Real) * a ^ (-5 / 2 : Real) * S₃) :=
      mul_le_mul hs_norm htail (norm_nonneg _) (by positivity)
    _ ≤ (3 * T) *
        ((3 / (4 * Real.pi ^ 2) : Real) *
            (3 * T / Real.pi) ^ (-3 / 2 : Real) * S₂ +
          (9 * (2 * T) / (80 * Real.pi ^ 3) : Real) *
            (3 * T / Real.pi) ^ (-5 / 2 : Real) * S₃) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hterm3 hterm5) (by positivity)
    _ = K / Real.sqrt T := by
      have hx : 3 * T / Real.pi = T * c := by dsimp [c]; field_simp [Real.pi_ne_zero]
      have hT3 : T * T ^ (-3 / 2 : Real) = T ^ (-1 / 2 : Real) := by
        calc
          T * T ^ (-3 / 2 : Real) = T ^ (1 : Real) * T ^ (-3 / 2 : Real) := by
            rw [Real.rpow_one]
          _ = T ^ ((1 : Real) + (-3 / 2 : Real)) :=
            (Real.rpow_add hT_pos 1 (-3 / 2 : Real)).symm
          _ = T ^ (-1 / 2 : Real) := by norm_num
      have hT5 : T * T * T ^ (-5 / 2 : Real) = T ^ (-1 / 2 : Real) := by
        calc
          T * T * T ^ (-5 / 2 : Real) =
              T ^ (2 : Real) * T ^ (-5 / 2 : Real) := by
                rw [Real.rpow_two, pow_two]
          _ = T ^ ((2 : Real) + (-5 / 2 : Real)) :=
            (Real.rpow_add hT_pos 2 (-5 / 2 : Real)).symm
          _ = T ^ (-1 / 2 : Real) := by norm_num
      have hThalf : T ^ (-1 / 2 : Real) = 1 / Real.sqrt T := by
        rw [show (-1 / 2 : Real) = -(1 / 2 : Real) by ring]
        rw [Real.rpow_neg hT_pos.le]
        rw [← Real.sqrt_eq_rpow]
        simp only [one_div]
      rw [hx, Real.mul_rpow hT_pos.le hc_pos.le,
        Real.mul_rpow hT_pos.le hc_pos.le]
      dsimp only [K]
      rw [show (9 * (2 * T) / (80 * Real.pi ^ 3) : Real) =
          2 * T * (9 / (80 * Real.pi ^ 3)) by ring]
      calc
        3 * T *
            (3 / (4 * Real.pi ^ 2) *
                (T ^ (-3 / 2 : Real) * c ^ (-3 / 2 : Real)) * S₂ +
              2 * T * (9 / (80 * Real.pi ^ 3)) *
                (T ^ (-5 / 2 : Real) * c ^ (-5 / 2 : Real)) * S₃) =
            (3 * (3 / (4 * Real.pi ^ 2)) * c ^ (-3 / 2 : Real) * S₂) *
                (T * T ^ (-3 / 2 : Real)) +
              (6 * (9 / (80 * Real.pi ^ 3)) * c ^ (-5 / 2 : Real) * S₃) *
                (T * T * T ^ (-5 / 2 : Real)) := by ring
        _ = K * (1 / Real.sqrt T) := by
          rw [hT3, hT5, hThalf]
          dsimp only [K]
          ring
        _ = K / Real.sqrt T := by ring

/--
Titchmarsh's uniform first approximation on the critical line, with the exact
project cutoff `n ≤ floor (3T/π)` and a fixed `T⁻¹ᐟ²` error constant.
-/
theorem exists_uniform_zetaFirstApproximation :
    ∃ K : Real, 0 < K ∧ ∃ T₀ : Real, 2 ≤ T₀ ∧
      ∀ T t : Real, T₀ ≤ T → T ≤ t → t ≤ 2 * T →
        ‖riemannZeta (((1 / 2 : Real) : Complex) + t * Complex.I) -
          ∑ k ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
            (k : Complex) ^
              (-(((1 / 2 : Real) : Complex) + t * Complex.I))‖ ≤
          K / Real.sqrt T := by
  let c : Real := 3 / Real.pi
  let S₂ : Real := ∑' n : Int, 1 / |(n : Real)| ^ 2
  let S₃ : Real := ∑' n : Int, 1 / |(n : Real)| ^ 3
  let Ktail : Real :=
    3 * (3 / (4 * Real.pi ^ 2)) * c ^ (-3 / 2 : Real) * S₂ +
      6 * (9 / (80 * Real.pi ^ 3)) * c ^ (-5 / 2 : Real) * S₃
  let K : Real := 4 + Ktail
  have hS₂ : 0 ≤ S₂ := tsum_nonneg fun n => by positivity
  have hS₃ : 0 ≤ S₃ := tsum_nonneg fun n => by positivity
  have hKtail : 0 ≤ Ktail := by
    dsimp only [Ktail]
    positivity
  have hK : 0 < K := by dsimp only [K]; linarith
  refine ⟨K, hK, 4, by norm_num, ?_⟩
  intro T t hT ht ht'
  let s : Complex := ((1 / 2 : Real) : Complex) + t * Complex.I
  let m : Nat := zetaFirstApproximationCutoff T
  let a : Real := (m : Real) + 1
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have ht_pos : 0 < t := hT_pos.trans_le ht
  have hExact := riemannZeta_criticalLine_eq_cutoffSum_add_sawtoothTail
    (T := T) ht_pos
  have hPole := norm_zetaFirstApproximation_cutoffSuccessorPole_le hT ht
  have hBoundary := norm_zetaFirstApproximation_cutoffBoundaryCorrection_le
    (t := t) hT_pos
  have hTail := norm_zetaFirstApproximation_cutoffSawtoothTail_le hT ht ht'
  dsimp only at hPole hTail
  change ‖(a : Complex) ^ (1 - s) / (s - 1)‖ ≤
      2 / Real.sqrt T at hPole
  change ‖((1 / 2 : Real) : Complex) * (a : Complex) ^ (-s)‖ ≤
      1 / Real.sqrt T at hBoundary
  change ‖s * ∫ u in Set.Ioi a,
      zetaFirstApproximationSawtoothTailIntegrand t u‖ ≤
        Ktail / Real.sqrt T at hTail
  change ‖riemannZeta s -
      ∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s)‖ ≤ K / Real.sqrt T
  change riemannZeta s =
      (∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s)) +
        (a : Complex) ^ (1 - s) / (s - 1) +
        (1 / 2 : Complex) * (a : Complex) ^ (-s) -
        s * ∫ u in Set.Ioi a,
          zetaFirstApproximationSawtoothTailIntegrand t u at hExact
  rw [hExact]
  have htriangle :
      ‖((∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s)) +
          (a : Complex) ^ (1 - s) / (s - 1) +
          (1 / 2 : Complex) * (a : Complex) ^ (-s) -
          s * ∫ u in Set.Ioi a,
            zetaFirstApproximationSawtoothTailIntegrand t u) -
          ∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-s)‖ ≤
        ‖(a : Complex) ^ (1 - s) / (s - 1)‖ +
          ‖((1 / 2 : Real) : Complex) * (a : Complex) ^ (-s)‖ +
          ‖s * ∫ u in Set.Ioi a,
            zetaFirstApproximationSawtoothTailIntegrand t u‖ := by
    calc
      _ = ‖((a : Complex) ^ (1 - s) / (s - 1) +
            (1 / 2 : Complex) * (a : Complex) ^ (-s)) -
            s * ∫ u in Set.Ioi a,
              zetaFirstApproximationSawtoothTailIntegrand t u‖ := by
        congr 1
        ring
      _ ≤ ‖(a : Complex) ^ (1 - s) / (s - 1) +
              (1 / 2 : Complex) * (a : Complex) ^ (-s)‖ +
            ‖s * ∫ u in Set.Ioi a,
              zetaFirstApproximationSawtoothTailIntegrand t u‖ := norm_sub_le _ _
      _ ≤ _ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (norm_add_le
            ((a : Complex) ^ (1 - s) / (s - 1))
            ((1 / 2 : Complex) * (a : Complex) ^ (-s)))
            ‖s * ∫ u in Set.Ioi a,
              zetaFirstApproximationSawtoothTailIntegrand t u‖)
  calc
    _ ≤ ‖(a : Complex) ^ (1 - s) / (s - 1)‖ +
          ‖((1 / 2 : Real) : Complex) * (a : Complex) ^ (-s)‖ +
          ‖s * ∫ u in Set.Ioi a,
            zetaFirstApproximationSawtoothTailIntegrand t u‖ := htriangle
    _ ≤ 2 / Real.sqrt T + 1 / Real.sqrt T + Ktail / Real.sqrt T :=
      add_le_add (add_le_add hPole hBoundary) hTail
    _ = (3 + Ktail) / Real.sqrt T := by ring
    _ ≤ K / Real.sqrt T := by
      apply div_le_div_of_nonneg_right
      · dsimp only [K]
        linarith
      · exact Real.sqrt_nonneg T

/--
The pole-correction term in Titchmarsh's first approximation is absorbed by
the final `T⁻¹ᐟ²` remainder on the critical line.

The constant `1` is sufficient because `3 / π < 1` and `t ≥ T`.
-/
theorem norm_zetaFirstApproximation_poleCorrection_le
    {T t : Real} (hT : 0 < T) (ht : T ≤ t) :
    ‖(((3 * T / Real.pi : Real) : Complex) ^
          (1 - ((1 / 2 : Real) : Complex) - t * Complex.I) /
        (((1 / 2 : Real) : Complex) + t * Complex.I - 1))‖ ≤
      1 / Real.sqrt T := by
  let x : Real := 3 * T / Real.pi
  let s : Complex := ((1 / 2 : Real) : Complex) + t * Complex.I
  have ht_nonneg : 0 ≤ t := hT.le.trans ht
  have hx_pos : 0 < x := by dsimp [x]; positivity
  have hx_le_T : x ≤ T := by
    dsimp [x]
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three, hT]
  have hden : t ≤ ‖s - 1‖ := by
    calc
      t = |(s - 1).im| := by simp [s, abs_of_nonneg ht_nonneg]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hden_pos : 0 < ‖s - 1‖ := hT.trans_le (ht.trans hden)
  have hnum : ‖(x : Complex) ^ (1 - s)‖ = Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    norm_num [s]
    exact (Real.sqrt_eq_rpow x).symm
  have hsqrt_le : Real.sqrt x ≤ Real.sqrt T :=
    Real.sqrt_le_sqrt hx_le_T
  have hsqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hquot :
      ‖(x : Complex) ^ (1 - s)‖ / ‖s - 1‖ ≤
        Real.sqrt T / T := by
    rw [hnum]
    exact div_le_div₀ (Real.sqrt_nonneg T) hsqrt_le hT (ht.trans hden)
  have hsqrt_div : Real.sqrt T / T = 1 / Real.sqrt T := by
    rw [div_eq_iff hT.ne']
    field_simp [hsqrt_pos.ne']
    exact Real.sq_sqrt hT.le
  calc
    _ = ‖(x : Complex) ^ (1 - s) / (s - 1)‖ := by
      congr 2
      all_goals
        dsimp only [x, s]
        ring_nf
    _ = ‖(x : Complex) ^ (1 - s)‖ / ‖s - 1‖ := norm_div _ _
    _ ≤ Real.sqrt T / T := hquot
    _ = 1 / Real.sqrt T := hsqrt_div

end

end Hardy

end RiemannHypothesisProject
