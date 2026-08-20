import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointComparisonEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointCompleteSineTransformEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointConvolutionEnclosures

/-!
# DF0 sharp form-comparison enclosures for M100-DF6D4

This module reconstructs the frozen cutoff-44 constants used to prove
`F_8 ≥ (2/5) E_8 ≥ 2 I`.  The leakage fraction is evaluated from the 89
quarter-period sinc-square primitives, while the smooth-Gamma remainder,
primitive norm, source scalar, and first-prime norm are composed from the
already admitted endpoint constants.  The final margin is exact rational
interval arithmetic.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## Quarter-period sine-integral values for the leakage sum -/

def suzukiDF6D4DF0QuarterWave (q : Nat) : Real :=
  ((q : Real) / 2) * Real.pi

def suzukiDF6D4DF0QuarterWaveInterval (q : Nat) : RationalInterval :=
  RationalInterval.scale (q / 2 : Rat) suzukiDF6D4PiInterval

theorem suzukiDF6D4DF0QuarterWaveInterval_contains (q : Nat) :
    (suzukiDF6D4DF0QuarterWaveInterval q).Contains
      (suzukiDF6D4DF0QuarterWave q) := by
  have h := RationalInterval.contains_scale (q / 2 : Rat)
    suzukiDF6D4PiInterval_contains
  unfold suzukiDF6D4DF0QuarterWaveInterval suzukiDF6D4DF0QuarterWave
  simpa using h

theorem suzukiDF6D4DF0QuarterWaveInterval_lower_pos
    (q : Nat) (hq : 1 ≤ q) :
    0 < (suzukiDF6D4DF0QuarterWaveInterval q).lower := by
  unfold suzukiDF6D4DF0QuarterWaveInterval RationalInterval.scale
  have hqRat : (0 : Rat) ≤ q / 2 := by positivity
  have hpi : suzukiDF6D4PiInterval.lower ≤ suzukiDF6D4PiInterval.upper := by
    native_decide
  rw [min_eq_left (mul_le_mul_of_nonneg_left hpi hqRat)]
  unfold suzukiDF6D4PiInterval
  positivity

def suzukiDF6D4DF0QuarterInversePowerInterval
    (q power : Nat) : RationalInterval :=
  (RationalInterval.point 1).divNonneg
    ((suzukiDF6D4DF0QuarterWaveInterval q).powNonneg power)

theorem suzukiDF6D4DF0QuarterInversePowerInterval_contains
    (q power : Nat) (hq : 1 ≤ q) :
    (suzukiDF6D4DF0QuarterInversePowerInterval q power).Contains
      (1 / suzukiDF6D4DF0QuarterWave q ^ power) := by
  have hwave := suzukiDF6D4DF0QuarterWaveInterval_contains q
  have hpow := RationalInterval.contains_powNonneg power
    (suzukiDF6D4DF0QuarterWaveInterval_lower_pos q hq).le hwave
  have hone : (RationalInterval.point 1).Contains (1 : Real) := by
    simpa using RationalInterval.contains_point 1
  have hdenPos :
      0 < ((suzukiDF6D4DF0QuarterWaveInterval q).powNonneg power).lower := by
    unfold RationalInterval.powNonneg
    exact pow_pos (suzukiDF6D4DF0QuarterWaveInterval_lower_pos q hq) power
  exact RationalInterval.contains_divNonneg
    (by norm_num [RationalInterval.point]) hdenPos hone hpow

/-- `sin(q*pi/2)` for the odd positive integers occurring in the leakage
sum. -/
def suzukiDF6D4DF0QuarterSineSign (q : Nat) : Rat :=
  if q % 4 = 1 then 1 else -1

def suzukiDF6D4DF0QuarterSineTailPolynomial (q : Nat) : Real :=
  let x := suzukiDF6D4DF0QuarterWave q
  ((suzukiDF6D4DF0QuarterSineSign q : Rat) : Real) *
    (1 / x ^ 2 - 6 / x ^ 4 + 120 / x ^ 6 - 5040 / x ^ 8 +
      362880 / x ^ 10)

def suzukiDF6D4DF0QuarterSineTail (q : Nat) : Real :=
  suzukiDF6D4DF0QuarterSineTailPolynomial q -
    3628800 *
      (∫ t : Real in Ioi (suzukiDF6D4DF0QuarterWave q),
        Real.sin t / t ^ 11)

def suzukiDF6D4DF0QuarterSineTailPolynomialInterval
    (q : Nat) : RationalInterval :=
  let base :=
    (((suzukiDF6D4DF0QuarterInversePowerInterval q 2).sub
      (RationalInterval.scale 6
        (suzukiDF6D4DF0QuarterInversePowerInterval q 4))).add
      (RationalInterval.scale 120
        (suzukiDF6D4DF0QuarterInversePowerInterval q 6))).sub
      (RationalInterval.scale 5040
        (suzukiDF6D4DF0QuarterInversePowerInterval q 8))
  RationalInterval.scale (suzukiDF6D4DF0QuarterSineSign q)
    (base.add (RationalInterval.scale 362880
      (suzukiDF6D4DF0QuarterInversePowerInterval q 10)))

def suzukiDF6D4DF0QuarterSineTailRadius (q : Nat) : Rat :=
  (RationalInterval.scale 362880
    (suzukiDF6D4DF0QuarterInversePowerInterval q 10)).upper

def suzukiDF6D4DF0QuarterSineTailInterval (q : Nat) : RationalInterval :=
  (suzukiDF6D4DF0QuarterSineTailPolynomialInterval q).add
    (RationalInterval.symmetric
      (suzukiDF6D4DF0QuarterSineTailRadius q))

theorem suzukiDF6D4DF0QuarterSineTailInterval_contains
    (q : Nat) (hq : 1 ≤ q) :
    (suzukiDF6D4DF0QuarterSineTailInterval q).Contains
      (suzukiDF6D4DF0QuarterSineTail q) := by
  let x := suzukiDF6D4DF0QuarterWave q
  have hx : 0 < x := by
    unfold x suzukiDF6D4DF0QuarterWave
    positivity
  have h2 := suzukiDF6D4DF0QuarterInversePowerInterval_contains q 2 hq
  have h4 := suzukiDF6D4DF0QuarterInversePowerInterval_contains q 4 hq
  have h6 := suzukiDF6D4DF0QuarterInversePowerInterval_contains q 6 hq
  have h8 := suzukiDF6D4DF0QuarterInversePowerInterval_contains q 8 hq
  have h10 := suzukiDF6D4DF0QuarterInversePowerInterval_contains q 10 hq
  have hbase := RationalInterval.contains_add
    (RationalInterval.contains_sub
      (RationalInterval.contains_add
        (RationalInterval.contains_sub h2
          (RationalInterval.contains_scale 6 h4))
        (RationalInterval.contains_scale 120 h6))
      (RationalInterval.contains_scale 5040 h8))
    (RationalInterval.contains_scale 362880 h10)
  have hpoly := RationalInterval.contains_scale
    (suzukiDF6D4DF0QuarterSineSign q) hbase
  have htail := suzukiDF6D4_abs_sin_tail_eleventh_le hx
  have hrem :
      abs (-3628800 * (∫ t : Real in Ioi x, Real.sin t / t ^ 11)) ≤
        362880 / x ^ 10 := by
    calc
      abs (-3628800 * (∫ t : Real in Ioi x, Real.sin t / t ^ 11)) =
          3628800 * abs (∫ t : Real in Ioi x, Real.sin t / t ^ 11) := by
        rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : Real) ≤ 3628800)]
      _ ≤ 3628800 * (1 / (10 * x ^ 10)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = 362880 / x ^ 10 := by ring
  have hradiusContains := RationalInterval.contains_scale 362880 h10
  have hradiusUpper :
      362880 / x ^ 10 ≤ (suzukiDF6D4DF0QuarterSineTailRadius q : Rat) := by
    unfold suzukiDF6D4DF0QuarterSineTailRadius
    convert hradiusContains.2 using 1 <;> norm_num [x, div_eq_mul_inv]
  have hremInterval := RationalInterval.contains_symmetric_of_abs_le
    (hrem.trans hradiusUpper)
  have htotal := RationalInterval.contains_add hpoly hremInterval
  unfold suzukiDF6D4DF0QuarterSineTailInterval
    suzukiDF6D4DF0QuarterSineTail
  dsimp [suzukiDF6D4DF0QuarterSineTailPolynomialInterval,
    suzukiDF6D4DF0QuarterSineTailPolynomial]
  change _
  convert htotal using 1 <;> ring

/-! The asymptotic tail is sharp from `q = 5` onward.  At the two small odd
arguments `q = 1,3`, the convergent sine-integral series is used instead. -/

noncomputable def suzukiDF6D4DF0SineIntegralMagnitude
    (x : Real) (n : Nat) : Real :=
  x ^ (2 * n + 1) /
    ((2 * n + 1 : Nat) * (2 * n + 1).factorial : Nat)

private theorem suzukiDF6D4DF0SineIntegralMagnitude_tail_antitone
    {x : Real} (hx0 : 0 ≤ x) (hx42 : x ^ 2 ≤ 42) :
    Antitone (fun n : Nat =>
      suzukiDF6D4DF0SineIntegralMagnitude x (n + 2)) := by
  apply antitone_nat_of_succ_le
  intro n
  let m : Nat := 2 * (n + 2) + 1
  have hm : 5 ≤ m := by omega
  have hfactorial :
      (m + 2).factorial = (m + 2) * (m + 1) * m.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hmpos : (0 : Real) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hm)
  have hxbound : x ^ 2 ≤ (m + 1 : Real) * (m + 2) := by
    have hmReal : (5 : Real) ≤ m := by exact_mod_cast hm
    calc
      x ^ 2 ≤ 42 := hx42
      _ ≤ (m + 1 : Real) * (m + 2) := by nlinarith
  have hcombined :
      x ^ 2 * (m : Real) ≤ (m + 2) ^ 2 * (m + 1) := by
    have h1 := mul_le_mul_of_nonneg_right hxbound hmpos.le
    have hmle : (m : Real) ≤ m + 2 := by norm_num
    nlinarith
  unfold suzukiDF6D4DF0SineIntegralMagnitude
  have hindex : 2 * (n + 1 + 2) + 1 = m + 2 := by
    dsimp [m]
    omega
  have hindex0 : 2 * (n + 2) + 1 = m := by rfl
  rw [hindex, hindex0, hfactorial]
  push_cast
  rw [pow_add]
  field_simp
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hcombined (pow_nonneg hx0 m)

private theorem summable_suzukiDF6D4DF0SineIntegralMagnitude
    {x : Real} (hx0 : 0 ≤ x) :
    Summable (suzukiDF6D4DF0SineIntegralMagnitude x) := by
  have hs := (Real.hasSum_sinh x).summable
  apply Summable.of_nonneg_of_le
    (fun n => by
      unfold suzukiDF6D4DF0SineIntegralMagnitude
      positivity) _ hs
  intro n
  unfold suzukiDF6D4DF0SineIntegralMagnitude
  have hnum : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  apply div_le_div_of_nonneg_left hnum
  · positivity
  · push_cast
    have hfactor : (1 : Real) ≤ ((2 * n + 1 : Nat) : Real) := by
      exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
    have hfactorial :
        (0 : Real) ≤ (((2 * n + 1 : Nat).factorial : Nat) : Real) := by
      positivity
    nlinarith

noncomputable def suzukiDF6D4DF0SmallSineIntegral (x : Real) : Real :=
  suzukiDF6D4DF0SineIntegralMagnitude x 0 -
    suzukiDF6D4DF0SineIntegralMagnitude x 1 +
    ∑' n : Nat, (-1 : Real) ^ n *
      suzukiDF6D4DF0SineIntegralMagnitude x (n + 2)

private theorem suzukiDF6D4DF0SmallSineIntegral_error
    {x : Real} (hx0 : 0 ≤ x) (hx42 : x ^ 2 ≤ 42) :
    |suzukiDF6D4DF0SmallSineIntegral x -
      ∑ n ∈ Finset.range 26, (-1 : Real) ^ n *
        suzukiDF6D4DF0SineIntegralMagnitude x n| ≤
      suzukiDF6D4DF0SineIntegralMagnitude x 26 := by
  let g : Nat → Real := fun n =>
    suzukiDF6D4DF0SineIntegralMagnitude x (n + 2)
  have hg : Summable g :=
    (summable_suzukiDF6D4DF0SineIntegralMagnitude hx0).comp_injective (by
      intro a b h
      dsimp at h
      omega)
  have h := alternating_series_error_bound g
    (suzukiDF6D4DF0SineIntegralMagnitude_tail_antitone hx0 hx42) hg 24
  unfold suzukiDF6D4DF0SmallSineIntegral
  rw [show
      (∑ n ∈ Finset.range 26, (-1 : Real) ^ n *
          suzukiDF6D4DF0SineIntegralMagnitude x n) =
        suzukiDF6D4DF0SineIntegralMagnitude x 0 -
          suzukiDF6D4DF0SineIntegralMagnitude x 1 +
          ∑ n ∈ Finset.range 24, (-1 : Real) ^ n *
            suzukiDF6D4DF0SineIntegralMagnitude x (n + 2) by
    rw [show 26 = 2 + 24 by norm_num, Finset.sum_range_add]
    rw [show
        (∑ n ∈ Finset.range 2, (-1 : Real) ^ n *
          suzukiDF6D4DF0SineIntegralMagnitude x n) =
          suzukiDF6D4DF0SineIntegralMagnitude x 0 -
            suzukiDF6D4DF0SineIntegralMagnitude x 1 by
      norm_num [Finset.sum_range_succ]
      ring]
    apply congrArg (fun z : Real =>
      suzukiDF6D4DF0SineIntegralMagnitude x 0 -
        suzukiDF6D4DF0SineIntegralMagnitude x 1 + z)
    apply Finset.sum_congr rfl
    intro n hn
    simp only [pow_add]
    ring]
  dsimp [g] at h
  simpa only [add_sub_add_left_eq_sub] using h

def suzukiDF6D4DF0SineIntegralTaylorCoefficient (n : Nat) : Rat :=
  (-1 : Rat) ^ n /
    ((2 * n + 1 : Nat) * (2 * n + 1).factorial : Nat)

def suzukiDF6D4DF0SineIntegralTaylorPartial :
    Nat → RationalInterval → RationalInterval
  | 0, _ => RationalInterval.point 0
  | terms + 1, I =>
      (suzukiDF6D4DF0SineIntegralTaylorPartial terms I).add
        (RationalInterval.scale
          (suzukiDF6D4DF0SineIntegralTaylorCoefficient terms)
          (I.powNonneg (2 * terms + 1)))

theorem suzukiDF6D4DF0SineIntegralTaylorPartial_contains
    (terms : Nat) {I : RationalInterval} {x : Real}
    (hI0 : 0 ≤ I.lower) (hx : I.Contains x) :
    (suzukiDF6D4DF0SineIntegralTaylorPartial terms I).Contains
      (∑ n ∈ Finset.range terms, (-1 : Real) ^ n *
        suzukiDF6D4DF0SineIntegralMagnitude x n) := by
  induction terms with
  | zero =>
      simpa [suzukiDF6D4DF0SineIntegralTaylorPartial] using
        RationalInterval.contains_point 0
  | succ terms ih =>
      rw [Finset.sum_range_succ]
      have hpow := RationalInterval.contains_powNonneg
        (2 * terms + 1) hI0 hx
      have hterm := RationalInterval.contains_scale
        (suzukiDF6D4DF0SineIntegralTaylorCoefficient terms) hpow
      have hterm' :
          (RationalInterval.scale
            (suzukiDF6D4DF0SineIntegralTaylorCoefficient terms)
            (I.powNonneg (2 * terms + 1))).Contains
          ((-1 : Real) ^ terms *
            suzukiDF6D4DF0SineIntegralMagnitude x terms) := by
        convert hterm using 1
        unfold suzukiDF6D4DF0SineIntegralTaylorCoefficient
          suzukiDF6D4DF0SineIntegralMagnitude
        push_cast
        ring
      exact RationalInterval.contains_add ih hterm'

def suzukiDF6D4DF0SineIntegralTaylorError
    (terms : Nat) (I : RationalInterval) : Rat :=
  I.upper ^ (2 * terms + 1) /
    ((2 * terms + 1 : Nat) * (2 * terms + 1).factorial : Nat)

def suzukiDF6D4DF0SineIntegralTaylor
    (terms : Nat) (I : RationalInterval) : RationalInterval :=
  (suzukiDF6D4DF0SineIntegralTaylorPartial terms I).add
    (RationalInterval.symmetric
      (suzukiDF6D4DF0SineIntegralTaylorError terms I))

theorem suzukiDF6D4DF0SineIntegralTaylor_contains
    {I : RationalInterval} {x : Real}
    (hI0 : 0 ≤ I.lower) (hx42 : x ^ 2 ≤ 42) (hx : I.Contains x) :
    (suzukiDF6D4DF0SineIntegralTaylor 26 I).Contains
      (suzukiDF6D4DF0SmallSineIntegral x) := by
  have hI0Real : (0 : Real) ≤ (I.lower : Real) := by exact_mod_cast hI0
  have hx0 : 0 ≤ x := hI0Real.trans hx.1
  let P : Real := ∑ n ∈ Finset.range 26, (-1 : Real) ^ n *
    suzukiDF6D4DF0SineIntegralMagnitude x n
  have hP := suzukiDF6D4DF0SineIntegralTaylorPartial_contains 26 hI0 hx
  have herr := suzukiDF6D4DF0SmallSineIntegral_error hx0 hx42
  have hpow : x ^ 53 ≤ (I.upper : Real) ^ 53 :=
    pow_le_pow_left₀ hx0 hx.2 _
  have hdenPos :
      (0 : Real) < (((53 : Nat) * (53 : Nat).factorial : Nat) : Real) := by
    positivity
  have herrUpper :
      suzukiDF6D4DF0SineIntegralMagnitude x 26 ≤
        (suzukiDF6D4DF0SineIntegralTaylorError 26 I : Rat) := by
    unfold suzukiDF6D4DF0SineIntegralMagnitude
      suzukiDF6D4DF0SineIntegralTaylorError
    norm_num
    exact div_le_div_of_nonneg_right hpow hdenPos.le
  have hsym := RationalInterval.contains_symmetric_of_abs_le
    (herr.trans herrUpper)
  unfold suzukiDF6D4DF0SineIntegralTaylor
  convert RationalInterval.contains_add hP hsym using 1
  ring

def suzukiDF6D4DF0QuarterSineIntegral (q : Nat) : Real :=
  if q ≤ 3 then
    suzukiDF6D4DF0SmallSineIntegral (suzukiDF6D4DF0QuarterWave q)
  else
    Real.pi / 2 - suzukiDF6D4DF0QuarterSineTail q

def suzukiDF6D4DF0QuarterSineIntegralInterval
    (q : Nat) : RationalInterval :=
  if q ≤ 3 then
    suzukiDF6D4DF0SineIntegralTaylor 26
      (suzukiDF6D4DF0QuarterWaveInterval q)
  else
    (RationalInterval.scale (1 / 2) suzukiDF6D4PiInterval).sub
      (suzukiDF6D4DF0QuarterSineTailInterval q)

theorem suzukiDF6D4DF0QuarterSineIntegralInterval_contains
    (q : Nat) (hq : 1 ≤ q) :
    (suzukiDF6D4DF0QuarterSineIntegralInterval q).Contains
      (suzukiDF6D4DF0QuarterSineIntegral q) := by
  by_cases hsmall : q ≤ 3
  · have hwave := suzukiDF6D4DF0QuarterWaveInterval_contains q
    have hsq : suzukiDF6D4DF0QuarterWave q ^ 2 ≤ 42 := by
      have hupper :
          (suzukiDF6D4DF0QuarterWaveInterval q).upper ^ 2 ≤ (42 : Rat) := by
        interval_cases q <;> native_decide
      have hwave0 : 0 ≤ suzukiDF6D4DF0QuarterWave q := by
        unfold suzukiDF6D4DF0QuarterWave
        positivity
      have hpow := pow_le_pow_left₀ hwave0 hwave.2 2
      exact hpow.trans (by exact_mod_cast hupper)
    simp only [suzukiDF6D4DF0QuarterSineIntegralInterval,
      suzukiDF6D4DF0QuarterSineIntegral, if_pos hsmall]
    exact suzukiDF6D4DF0SineIntegralTaylor_contains
      (suzukiDF6D4DF0QuarterWaveInterval_lower_pos q hq).le
      hsq hwave
  · simp only [suzukiDF6D4DF0QuarterSineIntegralInterval,
      suzukiDF6D4DF0QuarterSineIntegral, if_neg hsmall]
    exact RationalInterval.contains_sub
      (by
        convert RationalInterval.contains_scale (1 / 2)
          suzukiDF6D4PiInterval_contains using 1 <;> ring)
      (suzukiDF6D4DF0QuarterSineTailInterval_contains q hq)

/-! ## The 89-term leakage fraction -/

def suzukiDF6D4DF0LeakageAbsNumerator (index : Nat) : Nat :=
  if index ≤ 68 then 273 - 4 * index else 4 * index - 273

def suzukiDF6D4DF0LeakageArgumentSign (index : Nat) : Rat :=
  if index ≤ 68 then 1 else -1

theorem suzukiDF6D4DF0LeakageAbsNumerator_pos
    (index : Nat) (hindex : index < 89) :
    1 ≤ suzukiDF6D4DF0LeakageAbsNumerator index := by
  interval_cases index <;> native_decide

def suzukiDF6D4DF0PiInverseSquaredInterval : RationalInterval :=
  suzukiDF6D4PiInverseInterval.powNonneg 2

theorem suzukiDF6D4DF0PiInverseSquaredInterval_contains :
    suzukiDF6D4DF0PiInverseSquaredInterval.Contains (Real.pi⁻¹ ^ 2) := by
  exact RationalInterval.contains_powNonneg 2
    suzukiDF6D4PiInverseInterval_lower_nonneg
    suzukiDF6D4PiInverseInterval_contains

def suzukiDF6D4DF0LeakagePrimitive (index : Nat) : Real :=
  let q := suzukiDF6D4DF0LeakageAbsNumerator index
  let sign := suzukiDF6D4DF0LeakageArgumentSign index
  ((sign : Rat) : Real) * suzukiDF6D4DF0QuarterSineIntegral q * Real.pi⁻¹ +
    (((-2 * sign / q : Rat) : Real) * (Real.pi⁻¹ ^ 2))

def suzukiDF6D4DF0LeakagePrimitiveInterval
    (index : Nat) : RationalInterval :=
  let q := suzukiDF6D4DF0LeakageAbsNumerator index
  let sign := suzukiDF6D4DF0LeakageArgumentSign index
  suzukiDF6D4PiInverseInterval.mulLeftNonneg
      (RationalInterval.scale sign
        (suzukiDF6D4DF0QuarterSineIntegralInterval q)) |>.add
    (RationalInterval.scale (-2 * sign / q)
      suzukiDF6D4DF0PiInverseSquaredInterval)

theorem suzukiDF6D4DF0LeakagePrimitiveInterval_contains
    (index : Nat) (hindex : index < 89) :
    (suzukiDF6D4DF0LeakagePrimitiveInterval index).Contains
      (suzukiDF6D4DF0LeakagePrimitive index) := by
  let q := suzukiDF6D4DF0LeakageAbsNumerator index
  let sign := suzukiDF6D4DF0LeakageArgumentSign index
  have hq : 1 ≤ q := suzukiDF6D4DF0LeakageAbsNumerator_pos index hindex
  have hsine := suzukiDF6D4DF0QuarterSineIntegralInterval_contains q hq
  have hsigned := RationalInterval.contains_scale sign hsine
  have hmain := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4PiInverseInterval_lower_nonneg
    suzukiDF6D4PiInverseInterval_contains hsigned
  have hcorrection := RationalInterval.contains_scale (-2 * sign / q)
    suzukiDF6D4DF0PiInverseSquaredInterval_contains
  have htotal := RationalInterval.contains_add hmain hcorrection
  unfold suzukiDF6D4DF0LeakagePrimitiveInterval
    suzukiDF6D4DF0LeakagePrimitive
  dsimp only [q, sign] at htotal ⊢
  convert htotal using 1 <;> ring

def suzukiDF6D4DF0LeakageFraction : Real :=
  2 * ((97 / 4 : Real) -
    ∑ index ∈ Finset.range 89, suzukiDF6D4DF0LeakagePrimitive index)

def suzukiDF6D4DF0LeakageFractionRawInterval : RationalInterval :=
  RationalInterval.scale 2
    ((RationalInterval.point (97 / 4)).sub
      (RationalInterval.sum (Finset.range 89)
        suzukiDF6D4DF0LeakagePrimitiveInterval))

def suzukiDF6D4DF0LeakageFractionInterval : RationalInterval :=
  RationalInterval.roundOut 1000000000000000
    suzukiDF6D4DF0LeakageFractionRawInterval

theorem suzukiDF6D4DF0LeakageFractionRawInterval_contains :
    suzukiDF6D4DF0LeakageFractionRawInterval.Contains
      suzukiDF6D4DF0LeakageFraction := by
  have hsum := RationalInterval.contains_sum
    (s := Finset.range 89)
    (f := suzukiDF6D4DF0LeakagePrimitiveInterval)
    (x := suzukiDF6D4DF0LeakagePrimitive)
    (fun index hindex =>
      suzukiDF6D4DF0LeakagePrimitiveInterval_contains index
        (Finset.mem_range.mp hindex))
  have hsub := RationalInterval.contains_sub
    (by simpa using RationalInterval.contains_point (97 / 4 : Rat)) hsum
  unfold suzukiDF6D4DF0LeakageFractionRawInterval
    suzukiDF6D4DF0LeakageFraction
  convert RationalInterval.contains_scale 2 hsub using 1 <;> ring

theorem suzukiDF6D4DF0LeakageFractionInterval_contains :
    suzukiDF6D4DF0LeakageFractionInterval.Contains
      suzukiDF6D4DF0LeakageFraction := by
  exact RationalInterval.contains_roundOut (by norm_num)
    suzukiDF6D4DF0LeakageFractionRawInterval_contains

/-! ## Local-energy lower constant -/

def suzukiDF6D4DF0LogThresholdInterval : RationalInterval :=
  (suzukiDF6D4LogNatInterval 97).sub
    (RationalInterval.scale 2 fineLogTwoInterval)

theorem suzukiDF6D4DF0LogThresholdInterval_contains :
    suzukiDF6D4DF0LogThresholdInterval.Contains (Real.log (97 / 4)) := by
  have h97 := suzukiDF6D4LogNatInterval_contains 97 (by norm_num) (by norm_num)
  have h := RationalInterval.contains_sub h97
    (RationalInterval.contains_scale 2 fineLogTwoInterval_contains)
  have hid : Real.log (97 / 4) = Real.log 97 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num : (97 : Real) ≠ 0)
      (by norm_num : (4 : Real) ≠ 0)]
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  unfold suzukiDF6D4DF0LogThresholdInterval
  rw [hid]
  convert h using 1 <;> norm_num

def suzukiDF6D4DF0HighWeight : Real :=
  Real.log (97 / 4) + Real.log Real.pi - Real.log suzukiProjectAStar +
    Real.eulerMascheroniConstant

def suzukiDF6D4DF0HighWeightInterval : RationalInterval :=
  (((suzukiDF6D4DF0LogThresholdInterval.add
    suzukiDF6D4LogPiInterval).sub
      suzukiDF6D4LogAStarInterval).add fineEulerInterval)

theorem suzukiDF6D4DF0HighWeightInterval_contains :
    suzukiDF6D4DF0HighWeightInterval.Contains
      suzukiDF6D4DF0HighWeight := by
  exact RationalInterval.contains_add
    (RationalInterval.contains_sub
      (RationalInterval.contains_add
        suzukiDF6D4DF0LogThresholdInterval_contains
        suzukiDF6D4LogPiInterval_contains)
      suzukiDF6D4LogAStarInterval_contains)
    fineEulerInterval_contains

def suzukiDF6D4DF0ExpNegEulerInterval : RationalInterval :=
  ⟨561459482 / 1000000000, 561459485 / 1000000000⟩

private theorem suzukiDF6D4DF0ExpNegEuler_lower :
    (561459482 / 1000000000 : Real) ≤
      Real.exp (-577215666 / 1000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-577215666 / 1000000000 : Real))
    (n := 22) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem suzukiDF6D4DF0ExpNegEuler_upper :
    Real.exp (-577215664 / 1000000000 : Real) ≤
      (561459485 / 1000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-577215664 / 1000000000 : Real))
    (n := 22) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem suzukiDF6D4DF0ExpNegEulerInterval_contains :
    suzukiDF6D4DF0ExpNegEulerInterval.Contains
      (Real.exp (-Real.eulerMascheroniConstant)) := by
  have heuler := fineEulerInterval_contains
  unfold fineEulerInterval RationalInterval.Contains at heuler
  norm_num at heuler
  have hNegLower :
      (-577215666 / 1000000000 : Real) ≤
        -Real.eulerMascheroniConstant := by
    linarith [heuler.2]
  have hNegUpper :
      -Real.eulerMascheroniConstant ≤
        (-577215664 / 1000000000 : Real) := by
    linarith [heuler.1]
  unfold suzukiDF6D4DF0ExpNegEulerInterval RationalInterval.Contains
  constructor
  · simpa using suzukiDF6D4DF0ExpNegEuler_lower.trans
      (Real.exp_le_exp.mpr hNegLower)
  · simpa using (Real.exp_le_exp.mpr hNegUpper).trans
      suzukiDF6D4DF0ExpNegEuler_upper

def suzukiDF6D4DF0ZeroCrossing : Real :=
  suzukiProjectAStar * Real.exp (-Real.eulerMascheroniConstant) * Real.pi⁻¹

def suzukiDF6D4DF0ZeroCrossingInterval : RationalInterval :=
  (fineAStarInterval.mulNonneg
      suzukiDF6D4DF0ExpNegEulerInterval).mulNonneg
    suzukiDF6D4PiInverseInterval

theorem suzukiDF6D4DF0ZeroCrossingInterval_contains :
    suzukiDF6D4DF0ZeroCrossingInterval.Contains
      suzukiDF6D4DF0ZeroCrossing := by
  have hfirst := RationalInterval.contains_mulNonneg
    (by norm_num [fineAStarInterval])
    (by norm_num [suzukiDF6D4DF0ExpNegEulerInterval])
    fineAStarInterval_contains suzukiDF6D4DF0ExpNegEulerInterval_contains
  exact RationalInterval.contains_mulNonneg
    (by native_decide)
    suzukiDF6D4PiInverseInterval_lower_nonneg hfirst
    suzukiDF6D4PiInverseInterval_contains

def suzukiDF6D4DF0NegativeWeightLoss : Real :=
  4 * suzukiDF6D4DF0ZeroCrossing ^ 3 /
    (9 * 44 * (1 - suzukiDF6D4DF0ZeroCrossing / 45) ^ 2)

def suzukiDF6D4DF0NegativeWeightLossInterval : RationalInterval :=
  let numerator := RationalInterval.scale 4
    (suzukiDF6D4DF0ZeroCrossingInterval.powNonneg 3)
  let gap := (RationalInterval.point 1).sub
    (RationalInterval.scale (1 / 45)
      suzukiDF6D4DF0ZeroCrossingInterval)
  let denominator := RationalInterval.scale (9 * 44)
    (gap.powNonneg 2)
  numerator.divNonneg denominator

theorem suzukiDF6D4DF0NegativeWeightLossInterval_contains :
    suzukiDF6D4DF0NegativeWeightLossInterval.Contains
      suzukiDF6D4DF0NegativeWeightLoss := by
  have hz := suzukiDF6D4DF0ZeroCrossingInterval_contains
  have hz0 : 0 ≤ suzukiDF6D4DF0ZeroCrossingInterval.lower := by
    native_decide
  have hpow := RationalInterval.contains_powNonneg 3 hz0 hz
  have hnum := RationalInterval.contains_scale 4 hpow
  have hscaled := RationalInterval.contains_scale (1 / 45) hz
  have hgap := RationalInterval.contains_sub
    (by simpa using RationalInterval.contains_point (1 : Rat)) hscaled
  let gap := (RationalInterval.point 1).sub
    (RationalInterval.scale (1 / 45)
      suzukiDF6D4DF0ZeroCrossingInterval)
  have hgap0 : 0 ≤ gap.lower := by native_decide
  have hgapPow := RationalInterval.contains_powNonneg 2 hgap0 hgap
  have hden := RationalInterval.contains_scale (9 * 44) hgapPow
  have hnum0 :
      0 ≤ (RationalInterval.scale 4
        (suzukiDF6D4DF0ZeroCrossingInterval.powNonneg 3)).lower := by
    native_decide
  have hdenPos :
      0 < (RationalInterval.scale (9 * 44) (gap.powNonneg 2)).lower := by
    native_decide
  have hquot := RationalInterval.contains_divNonneg hnum0 hdenPos hnum hden
  unfold suzukiDF6D4DF0NegativeWeightLossInterval
    suzukiDF6D4DF0NegativeWeightLoss
  dsimp only [gap] at hquot ⊢
  convert hquot using 1 <;> ring

def suzukiDF6D4DF0LocalEnergyLower : Real :=
  suzukiDF6D4DF0HighWeight * (1 - suzukiDF6D4DF0LeakageFraction) -
    suzukiDF6D4DF0NegativeWeightLoss

def suzukiDF6D4DF0LocalEnergyLowerInterval : RationalInterval :=
  (suzukiDF6D4DF0HighWeightInterval.mulNonneg
    ((RationalInterval.point 1).sub
      suzukiDF6D4DF0LeakageFractionInterval)).sub
    suzukiDF6D4DF0NegativeWeightLossInterval

theorem suzukiDF6D4DF0LocalEnergyLowerInterval_contains :
    suzukiDF6D4DF0LocalEnergyLowerInterval.Contains
      suzukiDF6D4DF0LocalEnergyLower := by
  have hweight := suzukiDF6D4DF0HighWeightInterval_contains
  have hgap := RationalInterval.contains_sub
    (by simpa using RationalInterval.contains_point (1 : Rat))
    suzukiDF6D4DF0LeakageFractionInterval_contains
  have hmul := RationalInterval.contains_mulNonneg
    (by native_decide) (by native_decide) hweight hgap
  exact RationalInterval.contains_sub hmul
    suzukiDF6D4DF0NegativeWeightLossInterval_contains

/-! ## Smooth-Gamma remainder norm -/

def suzukiDF6D4DF0RemainderSecondDerivative : Real :=
  -2 * Real.cosh suzukiProjectAStar +
    Real.exp (-suzukiProjectAStar) /
      (1 - (Real.exp (-suzukiProjectAStar)) ^ 4) -
    1 / (4 * suzukiProjectAStar)

def suzukiDF6D4DF0RemainderSecondDerivativeInterval : RationalInterval :=
  let expFour := fineExpNegAStarInterval.powNonneg 4
  let gap := (RationalInterval.point 1).sub expFour
  let quotient := fineExpNegAStarInterval.divNonneg gap
  let inverseFourA := (RationalInterval.scale 4 fineAStarInterval).invPos
  ((RationalInterval.scale (-2) suzukiDF6D4CoshAStarInterval).add
    quotient).sub inverseFourA

theorem suzukiDF6D4DF0RemainderSecondDerivativeInterval_contains :
    suzukiDF6D4DF0RemainderSecondDerivativeInterval.Contains
      suzukiDF6D4DF0RemainderSecondDerivative := by
  have hexp4 := RationalInterval.contains_powNonneg 4
    (by norm_num [fineExpNegAStarInterval]) fineExpNegAStarInterval_contains
  have hgap := RationalInterval.contains_sub
    (by simpa using RationalInterval.contains_point (1 : Rat)) hexp4
  let gap := (RationalInterval.point 1).sub
    (fineExpNegAStarInterval.powNonneg 4)
  have hquot := RationalInterval.contains_divNonneg
    (by norm_num [fineExpNegAStarInterval]) (by native_decide)
    fineExpNegAStarInterval_contains hgap
  have hfourA := RationalInterval.contains_scale 4 fineAStarInterval_contains
  have hinv := RationalInterval.contains_invPos
    (by norm_num [RationalInterval.scale, fineAStarInterval]) hfourA
  have htotal := RationalInterval.contains_sub
    (RationalInterval.contains_add
      (RationalInterval.contains_scale (-2)
        suzukiDF6D4CoshAStarInterval_contains)
      hquot) hinv
  unfold suzukiDF6D4DF0RemainderSecondDerivativeInterval
    suzukiDF6D4DF0RemainderSecondDerivative
  dsimp only [gap] at htotal ⊢
  convert htotal using 1 <;> ring

def suzukiDF6D4DF0RemainderVariation : Real :=
  2 * ((-7 / 4 : Real) - suzukiDF6D4DF0RemainderSecondDerivative)

def suzukiDF6D4DF0RemainderVariationInterval : RationalInterval :=
  RationalInterval.scale 2
    ((RationalInterval.point (-7 / 4)).sub
      suzukiDF6D4DF0RemainderSecondDerivativeInterval)

theorem suzukiDF6D4DF0RemainderVariationInterval_contains :
    suzukiDF6D4DF0RemainderVariationInterval.Contains
      suzukiDF6D4DF0RemainderVariation := by
  exact RationalInterval.contains_scale 2
    (RationalInterval.contains_sub
      (by simpa using RationalInterval.contains_point (-7 / 4 : Rat))
      suzukiDF6D4DF0RemainderSecondDerivativeInterval_contains)

def suzukiDF6D4DF0PrimitiveRadicand : Rat := 1 / (45 ^ 2) + 2 / 44

def suzukiDF6D4DF0PrimitiveSqrtInterval : RationalInterval :=
  ⟨214355715144334 / 1000000000000000,
    214355715144335 / 1000000000000000⟩

theorem suzukiDF6D4DF0PrimitiveSqrtInterval_contains :
    suzukiDF6D4DF0PrimitiveSqrtInterval.Contains
      (Real.sqrt (2047 / 44550 : Real)) := by
  have hsqrtSq : (Real.sqrt (2047 / 44550 : Real)) ^ 2 = 2047 / 44550 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt (2047 / 44550 : Real) :=
    Real.sqrt_nonneg _
  constructor
  · rw [show
        ((suzukiDF6D4DF0PrimitiveSqrtInterval.lower : Rat) : Real) =
          (214355715144334 / 1000000000000000 : Real) by
        norm_num [suzukiDF6D4DF0PrimitiveSqrtInterval]]
    have hlowerSq :
        (214355715144334 / 1000000000000000 : Real) ^ 2 <
          2047 / 44550 := by norm_num
    nlinarith
  · rw [show
        ((suzukiDF6D4DF0PrimitiveSqrtInterval.upper : Rat) : Real) =
          (214355715144335 / 1000000000000000 : Real) by
        norm_num [suzukiDF6D4DF0PrimitiveSqrtInterval]]
    have hupperSq :
        (2047 / 44550 : Real) <
          (214355715144335 / 1000000000000000 : Real) ^ 2 := by norm_num
    nlinarith

def suzukiDF6D4DF0PrimitiveNorm : Real :=
  suzukiProjectAStar * Real.pi⁻¹ *
    Real.sqrt (2047 / 44550 : Real)

def suzukiDF6D4DF0PrimitiveNormInterval : RationalInterval :=
  (fineAStarInterval.mulNonneg suzukiDF6D4PiInverseInterval).mulNonneg
    suzukiDF6D4DF0PrimitiveSqrtInterval

theorem suzukiDF6D4DF0PrimitiveNormInterval_contains :
    suzukiDF6D4DF0PrimitiveNormInterval.Contains
      suzukiDF6D4DF0PrimitiveNorm := by
  have hfirst := RationalInterval.contains_mulNonneg
    (by norm_num [fineAStarInterval])
    suzukiDF6D4PiInverseInterval_lower_nonneg
    fineAStarInterval_contains suzukiDF6D4PiInverseInterval_contains
  exact RationalInterval.contains_mulNonneg
    (by native_decide)
    (by norm_num [suzukiDF6D4DF0PrimitiveSqrtInterval]) hfirst
    suzukiDF6D4DF0PrimitiveSqrtInterval_contains

def suzukiDF6D4DF0RemainderNorm : Real :=
  suzukiDF6D4DF0RemainderVariation * suzukiDF6D4DF0PrimitiveNorm

def suzukiDF6D4DF0RemainderNormInterval : RationalInterval :=
  suzukiDF6D4DF0RemainderVariationInterval.mulNonneg
    suzukiDF6D4DF0PrimitiveNormInterval

theorem suzukiDF6D4DF0RemainderNormInterval_contains :
    suzukiDF6D4DF0RemainderNormInterval.Contains
      suzukiDF6D4DF0RemainderNorm := by
  exact RationalInterval.contains_mulNonneg
    (by native_decide) (by native_decide)
    suzukiDF6D4DF0RemainderVariationInterval_contains
    suzukiDF6D4DF0PrimitiveNormInterval_contains

/-! ## Final rational form-order margin -/

def suzukiDF6D4DF0Scalar : Real :=
  Real.log 2 + Real.log Real.pi + Real.eulerMascheroniConstant

def suzukiDF6D4DF0ScalarInterval : RationalInterval :=
  (fineLogTwoInterval.add suzukiDF6D4LogPiInterval).add fineEulerInterval

theorem suzukiDF6D4DF0ScalarInterval_contains :
    suzukiDF6D4DF0ScalarInterval.Contains suzukiDF6D4DF0Scalar := by
  exact RationalInterval.contains_add
    (RationalInterval.contains_add fineLogTwoInterval_contains
      suzukiDF6D4LogPiInterval_contains)
    fineEulerInterval_contains

def suzukiDF6D4DF0PrimeNorm : Real := Real.log 2 * (Real.sqrt 2)⁻¹

def suzukiDF6D4DF0PrimeNormInterval : RationalInterval :=
  fineLogTwoInterval.mulNonneg fineSqrtTwoInterval.invPos

theorem suzukiDF6D4DF0PrimeNormInterval_contains :
    suzukiDF6D4DF0PrimeNormInterval.Contains suzukiDF6D4DF0PrimeNorm := by
  have hinv := RationalInterval.contains_invPos
    (by norm_num [fineSqrtTwoInterval]) fineSqrtTwoInterval_contains
  exact RationalInterval.contains_mulNonneg
    (by norm_num [fineLogTwoInterval])
    (by norm_num [RationalInterval.invPos, fineSqrtTwoInterval])
    fineLogTwoInterval_contains hinv

def suzukiDF6D4DF0NormPenalty : Real :=
  suzukiDF6D4DF0Scalar + suzukiDF6D4DF0PrimeNorm +
    suzukiDF6D4DF0RemainderNorm

def suzukiDF6D4DF0NormPenaltyInterval : RationalInterval :=
  (suzukiDF6D4DF0ScalarInterval.add
    suzukiDF6D4DF0PrimeNormInterval).add
      suzukiDF6D4DF0RemainderNormInterval

theorem suzukiDF6D4DF0NormPenaltyInterval_contains :
    suzukiDF6D4DF0NormPenaltyInterval.Contains
      suzukiDF6D4DF0NormPenalty := by
  exact RationalInterval.contains_add
    (RationalInterval.contains_add suzukiDF6D4DF0ScalarInterval_contains
      suzukiDF6D4DF0PrimeNormInterval_contains)
    suzukiDF6D4DF0RemainderNormInterval_contains

def suzukiDF6D4DF0TwoFifthsMargin : Real :=
  (3 / 5 : Real) * suzukiDF6D4DF0LocalEnergyLower -
    suzukiDF6D4DF0NormPenalty

def suzukiDF6D4DF0TwoFifthsMarginInterval : RationalInterval :=
  (RationalInterval.scale (3 / 5)
    suzukiDF6D4DF0LocalEnergyLowerInterval).sub
      suzukiDF6D4DF0NormPenaltyInterval

theorem suzukiDF6D4DF0TwoFifthsMarginInterval_contains :
    suzukiDF6D4DF0TwoFifthsMarginInterval.Contains
      suzukiDF6D4DF0TwoFifthsMargin := by
  have h := RationalInterval.contains_sub
    (RationalInterval.contains_scale (3 / 5)
      suzukiDF6D4DF0LocalEnergyLowerInterval_contains)
    suzukiDF6D4DF0NormPenaltyInterval_contains
  unfold suzukiDF6D4DF0TwoFifthsMarginInterval
    suzukiDF6D4DF0TwoFifthsMargin
  convert h using 1 <;> norm_num

theorem suzukiDF6D4DF0LocalEnergyLower_gt_five :
    5 < suzukiDF6D4DF0LocalEnergyLower := by
  have h := suzukiDF6D4DF0LocalEnergyLowerInterval_contains.1
  have hgrid :
      (5 : Rat) < suzukiDF6D4DF0LocalEnergyLowerInterval.lower := by
    native_decide
  have hgridReal :
      (5 : Real) < (suzukiDF6D4DF0LocalEnergyLowerInterval.lower : Real) := by
    exact_mod_cast hgrid
  exact hgridReal.trans_le h

theorem suzukiDF6D4DF0TwoFifthsMargin_gt_one_tenth :
    (1 / 10 : Real) < suzukiDF6D4DF0TwoFifthsMargin := by
  have h := suzukiDF6D4DF0TwoFifthsMarginInterval_contains.1
  have hgrid :
      (1 / 10 : Rat) < suzukiDF6D4DF0TwoFifthsMarginInterval.lower := by
    native_decide
  have hgridReal :
      (((1 / 10 : Rat) : Real)) <
        (suzukiDF6D4DF0TwoFifthsMarginInterval.lower : Real) := by
    exact_mod_cast hgrid
  have hgridReal' :
      (1 / 10 : Real) <
        (suzukiDF6D4DF0TwoFifthsMarginInterval.lower : Real) := by
    convert hgridReal using 1 <;> norm_num
  exact hgridReal'.trans_le h

/-- Elementary endpoint assembly from the visible signed form identity and
the three directional estimates.  No positivity premise is hidden in a
certificate record. -/
theorem suzukiDF6D4DF0_form_ge_two_fifths
    {qF qE normSq prime remainder : Real}
    (hnorm : 0 ≤ normSq)
    (hidentity : qF = qE - suzukiDF6D4DF0Scalar * normSq +
      prime - remainder)
    (henergy : suzukiDF6D4DF0LocalEnergyLower * normSq ≤ qE)
    (hprime : abs prime ≤ suzukiDF6D4DF0PrimeNorm * normSq)
    (hremainder : abs remainder ≤ suzukiDF6D4DF0RemainderNorm * normSq) :
    (2 / 5 : Real) * qE +
        suzukiDF6D4DF0TwoFifthsMargin * normSq ≤ qF := by
  have hprimeLower :
      -suzukiDF6D4DF0PrimeNorm * normSq ≤ prime := by
    linarith [neg_abs_le prime]
  have hremainderUpper :
      remainder ≤ suzukiDF6D4DF0RemainderNorm * normSq := by
    linarith [le_abs_self remainder]
  rw [hidentity]
  unfold suzukiDF6D4DF0TwoFifthsMargin suzukiDF6D4DF0NormPenalty
  nlinarith

theorem suzukiDF6D4DF0_two_fifths_energy_ge_two
    {qE normSq : Real} (hnorm : 0 ≤ normSq)
    (henergy : suzukiDF6D4DF0LocalEnergyLower * normSq ≤ qE) :
    2 * normSq ≤ (2 / 5 : Real) * qE := by
  have hell := suzukiDF6D4DF0LocalEnergyLower_gt_five
  nlinarith

end

end RiemannHypothesisProject.Experiments.M100
