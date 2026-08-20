import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailEnclosures

/-!
# Comparison-energy entry enclosures for M100-DF6D4

This module evaluates the comparison sine transform and both parity-specific
comparison diagonals on the frozen modes.  Integer logarithms are reduced to
`log 2` plus the rapidly convergent atanh series.  The sine- and cosine-tail
values at `2 * pi * mode` use their five-term asymptotic representations with
the remaining absolutely integrable tails kept in the definitions and bounded
inside Lean.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set
open scoped BigOperators

open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## Integer logarithms on the frozen far band -/

def suzukiDF6D4LogNatExponent (mode : Nat) : Nat :=
  if mode < 64 then 5
  else if mode < 128 then 6
  else if mode < 256 then 7
  else 8

def suzukiDF6D4LogNatBase (mode : Nat) : Nat :=
  2 ^ suzukiDF6D4LogNatExponent mode

def suzukiDF6D4LogNatRatio (mode : Nat) : Rat :=
  (mode - suzukiDF6D4LogNatBase mode : Rat) /
    (mode + suzukiDF6D4LogNatBase mode : Rat)

def suzukiDF6D4LogNatSeriesTerms : Nat := 24

def suzukiDF6D4LogNatSeries (mode : Nat) : Rat :=
  ∑ i ∈ Finset.range suzukiDF6D4LogNatSeriesTerms,
    suzukiDF6D4LogNatRatio mode ^ (2 * i + 1) / (2 * i + 1)

def suzukiDF6D4LogNatRemainder (mode : Nat) : Rat :=
  suzukiDF6D4LogNatRatio mode ^
      (2 * suzukiDF6D4LogNatSeriesTerms + 1) /
    (1 - suzukiDF6D4LogNatRatio mode ^ 2)

def suzukiDF6D4LogNatCoreInterval (mode : Nat) : RationalInterval :=
  ⟨2 * suzukiDF6D4LogNatSeries mode,
    2 * (suzukiDF6D4LogNatSeries mode +
      suzukiDF6D4LogNatRemainder mode)⟩

def suzukiDF6D4LogNatInterval (mode : Nat) : RationalInterval :=
  (RationalInterval.scale (suzukiDF6D4LogNatExponent mode)
      fineLogTwoInterval).add
    (suzukiDF6D4LogNatCoreInterval mode)

theorem suzukiDF6D4LogNatBase_bounds
    (mode : Nat) (hlower : 45 ≤ mode) (hupper : mode ≤ 300) :
    suzukiDF6D4LogNatBase mode ≤ mode ∧
      mode < 2 * suzukiDF6D4LogNatBase mode := by
  interval_cases mode <;> native_decide

private theorem suzukiDF6D4LogNatSeries_cast (mode : Nat) :
    ((suzukiDF6D4LogNatSeries mode : Rat) : Real) =
      ∑ i ∈ Finset.range suzukiDF6D4LogNatSeriesTerms,
        ((suzukiDF6D4LogNatRatio mode : Rat) : Real) ^ (2 * i + 1) /
          (2 * i + 1) := by
  unfold suzukiDF6D4LogNatSeries
  push_cast
  rfl

private theorem suzukiDF6D4LogNatRemainder_cast (mode : Nat) :
    ((suzukiDF6D4LogNatRemainder mode : Rat) : Real) =
      ((suzukiDF6D4LogNatRatio mode : Rat) : Real) ^
          (2 * suzukiDF6D4LogNatSeriesTerms + 1) /
        (1 - ((suzukiDF6D4LogNatRatio mode : Rat) : Real) ^ 2) := by
  unfold suzukiDF6D4LogNatRemainder
  push_cast
  rfl

theorem suzukiDF6D4LogNatCoreInterval_contains
    (mode : Nat) (hlower : 45 ≤ mode) (hupper : mode ≤ 300) :
    (suzukiDF6D4LogNatCoreInterval mode).Contains
      (Real.log
        (((mode : Real) /
          (suzukiDF6D4LogNatBase mode : Nat)) : Real)) := by
  let x : Real := ((suzukiDF6D4LogNatRatio mode : Rat) : Real)
  obtain ⟨hbaseLower, hbaseUpper⟩ :=
    suzukiDF6D4LogNatBase_bounds mode hlower hupper
  have hbasePos : 0 < suzukiDF6D4LogNatBase mode := by
    unfold suzukiDF6D4LogNatBase
    positivity
  have hdenPos :
      (0 : Real) < mode + suzukiDF6D4LogNatBase mode := by
    exact_mod_cast Nat.add_pos_left (lt_of_lt_of_le (by norm_num) hlower) _
  have hxEq :
      x = ((mode : Real) - suzukiDF6D4LogNatBase mode) /
        ((mode : Real) + suzukiDF6D4LogNatBase mode) := by
    unfold x suzukiDF6D4LogNatRatio
    push_cast
    rfl
  have hx0 : 0 ≤ x := by
    rw [hxEq]
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hbaseLower)) hdenPos.le
  have hx1 : x < 1 := by
    rw [hxEq]
    apply (div_lt_one hdenPos).2
    have hbaseRealPos : (0 : Real) < suzukiDF6D4LogNatBase mode := by
      exact_mod_cast hbasePos
    linarith
  have hratio :
      (1 + x) / (1 - x) =
        (mode : Real) / suzukiDF6D4LogNatBase mode := by
    rw [hxEq]
    have hbaseRealPos : (0 : Real) < suzukiDF6D4LogNatBase mode := by
      exact_mod_cast hbasePos
    field_simp [hbaseRealPos.ne'] <;> ring
  have hlowerSeries := Real.sum_range_le_log_div hx0 hx1
    suzukiDF6D4LogNatSeriesTerms
  have hupperSeries := Real.log_div_le_sum_range_add hx0 hx1
    suzukiDF6D4LogNatSeriesTerms
  rw [hratio] at hlowerSeries hupperSeries
  unfold RationalInterval.Contains
  change
    (((2 * suzukiDF6D4LogNatSeries mode : Rat) : Real) ≤
        Real.log ((mode : Real) / suzukiDF6D4LogNatBase mode)) ∧
      Real.log ((mode : Real) / suzukiDF6D4LogNatBase mode) ≤
        (((2 * (suzukiDF6D4LogNatSeries mode +
          suzukiDF6D4LogNatRemainder mode) : Rat) : Real))
  simp only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add]
  have hseries :
      ((suzukiDF6D4LogNatSeries mode : Rat) : Real) =
        ∑ i ∈ Finset.range suzukiDF6D4LogNatSeriesTerms,
          x ^ (2 * i + 1) / (2 * i + 1) := by
    simpa only [x] using suzukiDF6D4LogNatSeries_cast mode
  have hremainder :
      ((suzukiDF6D4LogNatRemainder mode : Rat) : Real) =
        x ^ (2 * suzukiDF6D4LogNatSeriesTerms + 1) /
          (1 - x ^ 2) := by
    simpa only [x] using suzukiDF6D4LogNatRemainder_cast mode
  constructor
  · rw [hseries]
    nlinarith
  · rw [hseries, hremainder]
    nlinarith

theorem suzukiDF6D4LogNatInterval_contains
    (mode : Nat) (hlower : 45 ≤ mode) (hupper : mode ≤ 300) :
    (suzukiDF6D4LogNatInterval mode).Contains (Real.log mode) := by
  have hcore := suzukiDF6D4LogNatCoreInterval_contains
    mode hlower hupper
  have hlogTwo := RationalInterval.contains_scale
    (suzukiDF6D4LogNatExponent mode) fineLogTwoInterval_contains
  have hadd := RationalInterval.contains_add hlogTwo hcore
  have hmodePos : (0 : Real) < mode := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 45) hlower
  have hbasePos : (0 : Real) < suzukiDF6D4LogNatBase mode := by
    unfold suzukiDF6D4LogNatBase
    positivity
  have hlogBase :
      Real.log (suzukiDF6D4LogNatBase mode) =
        suzukiDF6D4LogNatExponent mode * Real.log 2 := by
    unfold suzukiDF6D4LogNatBase
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hidentity :
      (suzukiDF6D4LogNatExponent mode : Real) * Real.log 2 +
          Real.log ((mode : Real) / suzukiDF6D4LogNatBase mode) =
        Real.log mode := by
    rw [Real.log_div hmodePos.ne' hbasePos.ne', hlogBase]
    norm_num
  unfold suzukiDF6D4LogNatInterval
  convert hadd using 1
  exact hidentity.symm

/-! ## Fixed logarithmic constants -/

def suzukiDF6D4LogAStarInterval : RationalInterval :=
  ⟨-847048882416843 / 1000000000000000,
    -847048882416841 / 1000000000000000⟩

private theorem exp_logAStar_lower_le :
    Real.exp (-847048882416843 / 1000000000000000 : Real) ≤
      (42867814670054956 / 100000000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-847048882416843 / 1000000000000000 : Real))
    (n := 32) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem le_exp_logAStar_upper :
    (42867814670054957 / 100000000000000000 : Real) ≤
      Real.exp (-847048882416841 / 1000000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-847048882416841 / 1000000000000000 : Real))
    (n := 32) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem suzukiDF6D4LogAStarInterval_contains :
    suzukiDF6D4LogAStarInterval.Contains
      (Real.log suzukiProjectAStar) := by
  have hA := fineAStarInterval_contains
  have hAPos : 0 < suzukiProjectAStar := suzukiProjectAStar_pos
  have hLowerExp :
      Real.exp (-847048882416843 / 1000000000000000 : Real) ≤
        suzukiProjectAStar := by
    exact exp_logAStar_lower_le.trans (by
      simpa [fineAStarInterval, RationalInterval.Contains] using hA.1)
  have hUpperExp :
      suzukiProjectAStar ≤
        Real.exp (-847048882416841 / 1000000000000000 : Real) := by
    have hAUpper :
        suzukiProjectAStar ≤
          (42867814670054957 / 100000000000000000 : Real) := by
      simpa [fineAStarInterval, RationalInterval.Contains] using hA.2
    exact hAUpper.trans le_exp_logAStar_upper
  have hlogLower :
      (-847048882416843 / 1000000000000000 : Real) ≤
        Real.log suzukiProjectAStar := by
    apply Real.exp_le_exp.mp
    simpa [Real.exp_log hAPos] using hLowerExp
  have hlogUpper :
      Real.log suzukiProjectAStar ≤
        (-847048882416841 / 1000000000000000 : Real) := by
    apply Real.exp_le_exp.mp
    simpa [Real.exp_log hAPos] using hUpperExp
  unfold suzukiDF6D4LogAStarInterval RationalInterval.Contains
  convert And.intro hlogLower hlogUpper using 1 <;> norm_num

def suzukiDF6D4LogPiInterval : RationalInterval :=
  fineLogFourPiInterval.sub
    (RationalInterval.scale 2 fineLogTwoInterval)

theorem suzukiDF6D4LogPiInterval_contains :
    suzukiDF6D4LogPiInterval.Contains (Real.log Real.pi) := by
  have hsub := RationalInterval.contains_sub
    fineLogFourPiInterval_contains
    (RationalInterval.contains_scale 2 fineLogTwoInterval_contains)
  have hidentity :
      Real.log (4 * Real.pi) - 2 * Real.log 2 = Real.log Real.pi := by
    rw [Real.log_mul (by norm_num : (4 : Real) ≠ 0) Real.pi_ne_zero,
      show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  unfold suzukiDF6D4LogPiInterval
  convert hsub using 1
  exact hidentity.symm

/-! ## Sine- and cosine-tail asymptotics at integer periods -/

theorem suzukiDF6D4_abs_cos_tail_tenth_le
    {x : Real} (hx : 0 < x) :
    abs (∫ t : Real in Ioi x, Real.cos t / t ^ 10) ≤
      1 / (9 * x ^ 9) := by
  have hmajor : IntegrableOn (fun t : Real => t ^ (-10 : Real)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hx
  have hbound := MeasureTheory.norm_integral_le_of_norm_le hmajor
    (μ := volume.restrict (Ioi x))
    (f := fun t : Real => Real.cos t / t ^ 10)
    (g := fun t : Real => t ^ (-10 : Real))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := hx.trans ht
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos htpos 10)]
      rw [show t ^ (-10 : Real) = 1 / t ^ 10 by
        norm_num [Real.rpow_neg_ofNat, zpow_neg]
        rfl]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one t)
        (pow_nonneg htpos.le 10))
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-10 : Real) < -1) hx] at hbound
  rw [Real.norm_eq_abs] at hbound
  have hvalue :
      -x ^ ((-10 : Real) + 1) / ((-10 : Real) + 1) =
        1 / (9 * x ^ 9) := by
    rw [show (-10 : Real) + 1 = -9 by norm_num]
    norm_num [Real.rpow_neg_ofNat, zpow_neg]
    field_simp
  rw [hvalue] at hbound
  exact hbound

theorem suzukiDF6D4_abs_sin_tail_eleventh_le
    {x : Real} (hx : 0 < x) :
    abs (∫ t : Real in Ioi x, Real.sin t / t ^ 11) ≤
      1 / (10 * x ^ 10) := by
  have hmajor : IntegrableOn (fun t : Real => t ^ (-11 : Real)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hx
  have hbound := MeasureTheory.norm_integral_le_of_norm_le hmajor
    (μ := volume.restrict (Ioi x))
    (f := fun t : Real => Real.sin t / t ^ 11)
    (g := fun t : Real => t ^ (-11 : Real))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := hx.trans ht
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos htpos 11)]
      rw [show t ^ (-11 : Real) = 1 / t ^ 11 by
        norm_num [Real.rpow_neg_ofNat, zpow_neg]
        rfl]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one t)
        (pow_nonneg htpos.le 11))
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-11 : Real) < -1) hx] at hbound
  rw [Real.norm_eq_abs] at hbound
  have hvalue :
      -x ^ ((-11 : Real) + 1) / ((-11 : Real) + 1) =
        1 / (10 * x ^ 10) := by
    rw [show (-11 : Real) + 1 = -10 by norm_num]
    norm_num [Real.rpow_neg_ofNat, zpow_neg]
    field_simp
  rw [hvalue] at hbound
  exact hbound

theorem suzukiDF6D4_abs_cos_tail_eleventh_le
    {x : Real} (hx : 0 < x) :
    abs (∫ t : Real in Ioi x, Real.cos t / t ^ 11) ≤
      1 / (10 * x ^ 10) := by
  have hmajor : IntegrableOn (fun t : Real => t ^ (-11 : Real)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hx
  have hbound := MeasureTheory.norm_integral_le_of_norm_le hmajor
    (μ := volume.restrict (Ioi x))
    (f := fun t : Real => Real.cos t / t ^ 11)
    (g := fun t : Real => t ^ (-11 : Real))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := hx.trans ht
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos htpos 11)]
      rw [show t ^ (-11 : Real) = 1 / t ^ 11 by
        norm_num [Real.rpow_neg_ofNat, zpow_neg]
        rfl]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one t)
        (pow_nonneg htpos.le 11))
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-11 : Real) < -1) hx] at hbound
  rw [Real.norm_eq_abs] at hbound
  have hvalue :
      -x ^ ((-11 : Real) + 1) / ((-11 : Real) + 1) =
        1 / (10 * x ^ 10) := by
    rw [show (-11 : Real) + 1 = -10 by norm_num]
    norm_num [Real.rpow_neg_ofNat, zpow_neg]
    field_simp
  rw [hvalue] at hbound
  exact hbound

def suzukiDF6D4ComparisonWave (mode : Nat) : Real :=
  2 * mode * Real.pi

def suzukiDF6D4ComparisonWaveInterval (mode : Nat) : RationalInterval :=
  RationalInterval.scale (2 * mode) suzukiDF6D4PiInterval

theorem suzukiDF6D4ComparisonWaveInterval_contains (mode : Nat) :
    (suzukiDF6D4ComparisonWaveInterval mode).Contains
      (suzukiDF6D4ComparisonWave mode) := by
  have h := RationalInterval.contains_scale (2 * mode)
    suzukiDF6D4PiInterval_contains
  unfold suzukiDF6D4ComparisonWaveInterval suzukiDF6D4ComparisonWave
  convert h using 1 <;> norm_num

theorem suzukiDF6D4ComparisonWaveInterval_lower_pos
    (mode : Nat) (hmode : 1 ≤ mode) :
    0 < (suzukiDF6D4ComparisonWaveInterval mode).lower := by
  unfold suzukiDF6D4ComparisonWaveInterval RationalInterval.scale
  have hq : (0 : Rat) ≤ 2 * mode := by positivity
  have hpi :
      suzukiDF6D4PiInterval.lower ≤ suzukiDF6D4PiInterval.upper := by
    native_decide
  rw [min_eq_left (mul_le_mul_of_nonneg_left hpi hq)]
  unfold suzukiDF6D4PiInterval
  positivity

def suzukiDF6D4ComparisonInverseWavePowerInterval
    (mode power : Nat) : RationalInterval :=
  (RationalInterval.point 1).divNonneg
    ((suzukiDF6D4ComparisonWaveInterval mode).powNonneg power)

theorem suzukiDF6D4ComparisonInverseWavePowerInterval_contains
    (mode power : Nat) (hmode : 1 ≤ mode) :
    (suzukiDF6D4ComparisonInverseWavePowerInterval mode power).Contains
      (1 / suzukiDF6D4ComparisonWave mode ^ power) := by
  have hwave := suzukiDF6D4ComparisonWaveInterval_contains mode
  have hpow := RationalInterval.contains_powNonneg power
    (suzukiDF6D4ComparisonWaveInterval_lower_pos mode hmode).le hwave
  have hone : (RationalInterval.point 1).Contains (1 : Real) := by
    simpa using RationalInterval.contains_point 1
  have hdenPos :
      0 < ((suzukiDF6D4ComparisonWaveInterval mode).powNonneg power).lower := by
    unfold RationalInterval.powNonneg
    exact pow_pos (suzukiDF6D4ComparisonWaveInterval_lower_pos mode hmode) power
  unfold suzukiDF6D4ComparisonInverseWavePowerInterval
  exact RationalInterval.contains_divNonneg
    (by norm_num [RationalInterval.point]) hdenPos hone hpow

/-- The sine tail `π/2-Si(x)` in the exact five-term representation used by
the frozen comparison certificate. -/
def suzukiDF6D4ComparisonSineTail (mode : Nat) : Real :=
  let x := suzukiDF6D4ComparisonWave mode
  1 / x - 2 / x ^ 3 + 24 / x ^ 5 - 720 / x ^ 7 +
    40320 / x ^ 9 -
      362880 * (∫ t : Real in Ioi x, Real.cos t / t ^ 10)

/-- The negative cosine-integral tail `-Ci(x)` in the exact five-term
representation used by the frozen comparison certificate. -/
def suzukiDF6D4ComparisonCosineTail (mode : Nat) : Real :=
  let x := suzukiDF6D4ComparisonWave mode
  1 / x ^ 2 - 6 / x ^ 4 + 120 / x ^ 6 - 5040 / x ^ 8 +
    362880 / x ^ 10 -
      3628800 * (∫ t : Real in Ioi x, Real.cos t / t ^ 11)

def suzukiDF6D4ComparisonSineTailPolynomialInterval
    (mode : Nat) : RationalInterval :=
  (((suzukiDF6D4ComparisonInverseWavePowerInterval mode 1).sub
      (RationalInterval.scale 2
        (suzukiDF6D4ComparisonInverseWavePowerInterval mode 3))).add
      (RationalInterval.scale 24
        (suzukiDF6D4ComparisonInverseWavePowerInterval mode 5))).sub
      (RationalInterval.scale 720
        (suzukiDF6D4ComparisonInverseWavePowerInterval mode 7)) |>.add
      (RationalInterval.scale 40320
        (suzukiDF6D4ComparisonInverseWavePowerInterval mode 9))

def suzukiDF6D4ComparisonSineTailRemainderRadius (mode : Nat) : Rat :=
  (RationalInterval.scale 40320
    (suzukiDF6D4ComparisonInverseWavePowerInterval mode 9)).upper

def suzukiDF6D4ComparisonSineTailInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4ComparisonSineTailPolynomialInterval mode).add
    (RationalInterval.symmetric
      (suzukiDF6D4ComparisonSineTailRemainderRadius mode))

theorem suzukiDF6D4ComparisonSineTailInterval_contains
    (mode : Nat) (hmode : 1 ≤ mode) :
    (suzukiDF6D4ComparisonSineTailInterval mode).Contains
      (suzukiDF6D4ComparisonSineTail mode) := by
  let x := suzukiDF6D4ComparisonWave mode
  have hx : 0 < x := by
    unfold x suzukiDF6D4ComparisonWave
    positivity
  have h1 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 1 hmode
  have h3 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 3 hmode
  have h5 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 5 hmode
  have h7 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 7 hmode
  have h9 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 9 hmode
  have hpoly := RationalInterval.contains_add
    (RationalInterval.contains_sub
      (RationalInterval.contains_add
        (RationalInterval.contains_sub h1
          (RationalInterval.contains_scale 2 h3))
        (RationalInterval.contains_scale 24 h5))
      (RationalInterval.contains_scale 720 h7))
    (RationalInterval.contains_scale 40320 h9)
  have htail := suzukiDF6D4_abs_cos_tail_tenth_le hx
  have hrem :
      abs (-362880 * (∫ t : Real in Ioi x, Real.cos t / t ^ 10)) ≤
        40320 / x ^ 9 := by
    calc
      abs (-362880 * (∫ t : Real in Ioi x, Real.cos t / t ^ 10)) =
          362880 * abs (∫ t : Real in Ioi x, Real.cos t / t ^ 10) := by
        rw [abs_mul, abs_neg,
          abs_of_nonneg (by norm_num : (0 : Real) ≤ 362880)]
      _ ≤ 362880 * (1 / (9 * x ^ 9)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = 40320 / x ^ 9 := by ring
  have hradiusContains := RationalInterval.contains_scale 40320 h9
  have hradiusUpper :
      40320 / x ^ 9 ≤
        (suzukiDF6D4ComparisonSineTailRemainderRadius mode : Rat) := by
    unfold suzukiDF6D4ComparisonSineTailRemainderRadius
    convert hradiusContains.2 using 1 <;>
      norm_num [x, div_eq_mul_inv]
  have hremSymmetric := RationalInterval.contains_symmetric_of_abs_le
    (hrem.trans hradiusUpper)
  have htotal := RationalInterval.contains_add hpoly hremSymmetric
  unfold suzukiDF6D4ComparisonSineTailInterval
  unfold suzukiDF6D4ComparisonSineTailPolynomialInterval
  unfold suzukiDF6D4ComparisonSineTail
  change _
  convert htotal using 1 <;> ring

def suzukiDF6D4ComparisonCosineTailPolynomialInterval
    (mode : Nat) : RationalInterval :=
  (((suzukiDF6D4ComparisonInverseWavePowerInterval mode 2).sub
      (RationalInterval.scale 6
        (suzukiDF6D4ComparisonInverseWavePowerInterval mode 4))).add
      (RationalInterval.scale 120
        (suzukiDF6D4ComparisonInverseWavePowerInterval mode 6))).sub
      (RationalInterval.scale 5040
        (suzukiDF6D4ComparisonInverseWavePowerInterval mode 8)) |>.add
      (RationalInterval.scale 362880
        (suzukiDF6D4ComparisonInverseWavePowerInterval mode 10))

def suzukiDF6D4ComparisonCosineTailRemainderRadius (mode : Nat) : Rat :=
  (RationalInterval.scale 362880
    (suzukiDF6D4ComparisonInverseWavePowerInterval mode 10)).upper

def suzukiDF6D4ComparisonCosineTailInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4ComparisonCosineTailPolynomialInterval mode).add
    (RationalInterval.symmetric
      (suzukiDF6D4ComparisonCosineTailRemainderRadius mode))

theorem suzukiDF6D4ComparisonCosineTailInterval_contains
    (mode : Nat) (hmode : 1 ≤ mode) :
    (suzukiDF6D4ComparisonCosineTailInterval mode).Contains
      (suzukiDF6D4ComparisonCosineTail mode) := by
  let x := suzukiDF6D4ComparisonWave mode
  have hx : 0 < x := by
    unfold x suzukiDF6D4ComparisonWave
    positivity
  have h2 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 2 hmode
  have h4 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 4 hmode
  have h6 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 6 hmode
  have h8 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 8 hmode
  have h10 := suzukiDF6D4ComparisonInverseWavePowerInterval_contains mode 10 hmode
  have hpoly := RationalInterval.contains_add
    (RationalInterval.contains_sub
      (RationalInterval.contains_add
        (RationalInterval.contains_sub h2
          (RationalInterval.contains_scale 6 h4))
        (RationalInterval.contains_scale 120 h6))
      (RationalInterval.contains_scale 5040 h8))
    (RationalInterval.contains_scale 362880 h10)
  have htail := suzukiDF6D4_abs_cos_tail_eleventh_le hx
  have hrem :
      abs (-3628800 * (∫ t : Real in Ioi x, Real.cos t / t ^ 11)) ≤
        362880 / x ^ 10 := by
    calc
      abs (-3628800 * (∫ t : Real in Ioi x, Real.cos t / t ^ 11)) =
          3628800 * abs (∫ t : Real in Ioi x, Real.cos t / t ^ 11) := by
        rw [abs_mul, abs_neg,
          abs_of_nonneg (by norm_num : (0 : Real) ≤ 3628800)]
      _ ≤ 3628800 * (1 / (10 * x ^ 10)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = 362880 / x ^ 10 := by ring
  have hradiusContains := RationalInterval.contains_scale 362880 h10
  have hradiusUpper :
      362880 / x ^ 10 ≤
        (suzukiDF6D4ComparisonCosineTailRemainderRadius mode : Rat) := by
    unfold suzukiDF6D4ComparisonCosineTailRemainderRadius
    convert hradiusContains.2 using 1 <;>
      norm_num [x, div_eq_mul_inv]
  have hremSymmetric := RationalInterval.contains_symmetric_of_abs_le
    (hrem.trans hradiusUpper)
  have htotal := RationalInterval.contains_add hpoly hremSymmetric
  unfold suzukiDF6D4ComparisonCosineTailInterval
  unfold suzukiDF6D4ComparisonCosineTailPolynomialInterval
  unfold suzukiDF6D4ComparisonCosineTail
  change _
  convert htotal using 1 <;> ring

/-! ## Complete comparison transform and parity diagonals -/

def suzukiDF6D4ComparisonSineIntegral (mode : Nat) : Real :=
  Real.pi / 2 - suzukiDF6D4ComparisonSineTail mode

def suzukiDF6D4ComparisonSineTransform (mode : Nat) : Real :=
  -suzukiDF6D4ComparisonSineIntegral mode

def suzukiDF6D4ComparisonSineIntegralInterval
    (mode : Nat) : RationalInterval :=
  (RationalInterval.scale (1 / 2) suzukiDF6D4PiInterval).sub
    (suzukiDF6D4ComparisonSineTailInterval mode)

def suzukiDF6D4ComparisonSineTransformInterval
    (mode : Nat) : RationalInterval :=
  (suzukiDF6D4ComparisonSineIntegralInterval mode).neg

theorem suzukiDF6D4ComparisonSineIntegralInterval_contains
    (mode : Nat) (hmode : 1 ≤ mode) :
    (suzukiDF6D4ComparisonSineIntegralInterval mode).Contains
      (suzukiDF6D4ComparisonSineIntegral mode) := by
  exact RationalInterval.contains_sub
    (by
      convert RationalInterval.contains_scale (1 / 2)
        suzukiDF6D4PiInterval_contains using 1 <;> ring)
    (suzukiDF6D4ComparisonSineTailInterval_contains mode hmode)

theorem suzukiDF6D4ComparisonSineTransformInterval_contains
    (mode : Nat) (hmode : 1 ≤ mode) :
    (suzukiDF6D4ComparisonSineTransformInterval mode).Contains
      (suzukiDF6D4ComparisonSineTransform mode) := by
  exact RationalInterval.contains_neg
    (suzukiDF6D4ComparisonSineIntegralInterval_contains mode hmode)

def suzukiDF6D4ComparisonLogFrequencyInterval
    (mode : Nat) : RationalInterval :=
  ((suzukiDF6D4LogNatInterval mode).add
    suzukiDF6D4LogPiInterval).sub
      suzukiDF6D4LogAStarInterval

def suzukiDF6D4ComparisonDiagonalBaseInterval
    (mode : Nat) : RationalInterval :=
  ((suzukiDF6D4ComparisonLogFrequencyInterval mode).add
    fineEulerInterval).add
      (suzukiDF6D4ComparisonCosineTailInterval mode)

def suzukiDF6D4ComparisonSineOverWaveInterval
    (mode : Nat) : RationalInterval :=
  (suzukiDF6D4ComparisonInverseWavePowerInterval mode 1).mulLeftNonneg
    (suzukiDF6D4ComparisonSineIntegralInterval mode)

def suzukiDF6D4EvenComparisonDiagonal (mode : Nat) : Real :=
  Real.log mode + Real.log Real.pi - Real.log suzukiProjectAStar +
    Real.eulerMascheroniConstant +
    suzukiDF6D4ComparisonCosineTail mode +
    suzukiDF6D4ComparisonSineIntegral mode /
      suzukiDF6D4ComparisonWave mode

def suzukiDF6D4OddComparisonDiagonal (mode : Nat) : Real :=
  Real.log mode + Real.log Real.pi - Real.log suzukiProjectAStar +
    Real.eulerMascheroniConstant +
    suzukiDF6D4ComparisonCosineTail mode -
    suzukiDF6D4ComparisonSineIntegral mode /
      suzukiDF6D4ComparisonWave mode

def suzukiDF6D4EvenComparisonDiagonalInterval
    (mode : Nat) : RationalInterval :=
  (suzukiDF6D4ComparisonDiagonalBaseInterval mode).add
    (suzukiDF6D4ComparisonSineOverWaveInterval mode)

def suzukiDF6D4OddComparisonDiagonalInterval
    (mode : Nat) : RationalInterval :=
  (suzukiDF6D4ComparisonDiagonalBaseInterval mode).sub
    (suzukiDF6D4ComparisonSineOverWaveInterval mode)

private theorem suzukiDF6D4ComparisonDiagonalBaseInterval_contains
    (mode : Nat) (hlower : 45 ≤ mode) (hupper : mode ≤ 300) :
    (suzukiDF6D4ComparisonDiagonalBaseInterval mode).Contains
      (Real.log mode + Real.log Real.pi - Real.log suzukiProjectAStar +
        Real.eulerMascheroniConstant +
        suzukiDF6D4ComparisonCosineTail mode) := by
  have hlogFrequency := RationalInterval.contains_sub
    (RationalInterval.contains_add
      (suzukiDF6D4LogNatInterval_contains mode hlower hupper)
      suzukiDF6D4LogPiInterval_contains)
    suzukiDF6D4LogAStarInterval_contains
  exact RationalInterval.contains_add
    (RationalInterval.contains_add hlogFrequency fineEulerInterval_contains)
    (suzukiDF6D4ComparisonCosineTailInterval_contains mode
      (by omega))

private theorem suzukiDF6D4ComparisonSineOverWaveInterval_contains
    (mode : Nat) (hmode : 1 ≤ mode) :
    (suzukiDF6D4ComparisonSineOverWaveInterval mode).Contains
      (suzukiDF6D4ComparisonSineIntegral mode /
        suzukiDF6D4ComparisonWave mode) := by
  have hinv := suzukiDF6D4ComparisonInverseWavePowerInterval_contains
    mode 1 hmode
  have hsine := suzukiDF6D4ComparisonSineIntegralInterval_contains mode hmode
  have hwave := suzukiDF6D4ComparisonWaveInterval_contains mode
  have hwavePos : 0 < suzukiDF6D4ComparisonWave mode := by
    unfold suzukiDF6D4ComparisonWave
    positivity
  have hupperReal :
      0 < ((suzukiDF6D4ComparisonWaveInterval mode).upper : Real) :=
    hwavePos.trans_le hwave.2
  have hupperRat :
      0 < (suzukiDF6D4ComparisonWaveInterval mode).upper := by
    exact_mod_cast hupperReal
  have hnonneg :
      0 ≤ (suzukiDF6D4ComparisonInverseWavePowerInterval mode 1).lower := by
    unfold suzukiDF6D4ComparisonInverseWavePowerInterval
    unfold RationalInterval.divNonneg RationalInterval.mulNonneg
      RationalInterval.invPos RationalInterval.point
      RationalInterval.powNonneg
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (pow_nonneg hupperRat.le 1))
  have hmul := RationalInterval.contains_mulLeftNonneg hnonneg hinv hsine
  unfold suzukiDF6D4ComparisonSineOverWaveInterval
  convert hmul using 1
  unfold suzukiDF6D4ComparisonWave
  field_simp

theorem suzukiDF6D4EvenComparisonDiagonalInterval_contains
    (mode : Nat) (hlower : 45 ≤ mode) (hupper : mode ≤ 300) :
    (suzukiDF6D4EvenComparisonDiagonalInterval mode).Contains
      (suzukiDF6D4EvenComparisonDiagonal mode) := by
  have hbase := suzukiDF6D4ComparisonDiagonalBaseInterval_contains
    mode hlower hupper
  have hsine := suzukiDF6D4ComparisonSineOverWaveInterval_contains
    mode (by omega)
  unfold suzukiDF6D4EvenComparisonDiagonalInterval
  unfold suzukiDF6D4EvenComparisonDiagonal
  convert RationalInterval.contains_add hbase hsine using 1 <;> ring

theorem suzukiDF6D4OddComparisonDiagonalInterval_contains
    (mode : Nat) (hlower : 45 ≤ mode) (hupper : mode ≤ 300) :
    (suzukiDF6D4OddComparisonDiagonalInterval mode).Contains
      (suzukiDF6D4OddComparisonDiagonal mode) := by
  have hbase := suzukiDF6D4ComparisonDiagonalBaseInterval_contains
    mode hlower hupper
  have hsine := suzukiDF6D4ComparisonSineOverWaveInterval_contains
    mode (by omega)
  unfold suzukiDF6D4OddComparisonDiagonalInterval
  unfold suzukiDF6D4OddComparisonDiagonal
  convert RationalInterval.contains_sub hbase hsine using 1 <;> ring

/-! ## Frozen certificate grids -/

/-- Outward grid used for every comparison transform needed by the finite
Galerkin band and explicit residual prefix. -/
def suzukiDF6D4FrozenComparisonSineTransformInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 100000000000000
    (suzukiDF6D4ComparisonSineTransformInterval mode)

/-- Outward grid used for the even comparison-energy diagonal on the frozen
Galerkin range `45,...,300`. -/
def suzukiDF6D4FrozenEvenComparisonDiagonalInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 1000000000000
    (suzukiDF6D4EvenComparisonDiagonalInterval mode)

/-- Outward grid used for the odd comparison-energy diagonal on the frozen
Galerkin range `45,...,300`. -/
def suzukiDF6D4FrozenOddComparisonDiagonalInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 1000000000000
    (suzukiDF6D4OddComparisonDiagonalInterval mode)

theorem suzukiDF6D4FrozenComparisonSineTransformInterval_contains
    (mode : Nat) (hmode : 1 ≤ mode) :
    (suzukiDF6D4FrozenComparisonSineTransformInterval mode).Contains
      (suzukiDF6D4ComparisonSineTransform mode) := by
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4ComparisonSineTransformInterval_contains mode hmode)

theorem suzukiDF6D4FrozenEvenComparisonDiagonalInterval_contains
    (mode : Nat) (hlower : 45 ≤ mode) (hupper : mode ≤ 300) :
    (suzukiDF6D4FrozenEvenComparisonDiagonalInterval mode).Contains
      (suzukiDF6D4EvenComparisonDiagonal mode) := by
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4EvenComparisonDiagonalInterval_contains mode hlower hupper)

theorem suzukiDF6D4FrozenOddComparisonDiagonalInterval_contains
    (mode : Nat) (hlower : 45 ≤ mode) (hupper : mode ≤ 300) :
    (suzukiDF6D4FrozenOddComparisonDiagonalInterval mode).Contains
      (suzukiDF6D4OddComparisonDiagonal mode) := by
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4OddComparisonDiagonalInterval_contains mode hlower hupper)

end

end RiemannHypothesisProject.Experiments.M100
