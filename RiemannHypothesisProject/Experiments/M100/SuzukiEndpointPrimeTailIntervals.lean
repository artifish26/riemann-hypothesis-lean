import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualTailMain
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointPrimeSineEnclosures

/-!
# Exact rational intervals for the sharp prime-2 tail

This module reproduces the frozen FT3 oscillatory cutoff `20000`.  Modes
`601,...,20000` are evaluated by the proved prime-angle intervals, with every
weighted term rounded outward to a common rational grid.  The remaining
infinite sine and sine-square tails use the complete Dirichlet estimates.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators
open RationalInterval

def suzukiDF6D4PrimeTailFiniteCount : Nat := 19400

def suzukiDF6D4PrimeTailIntervalDenominator : Nat :=
  1000000000000000000000000

def suzukiDF6D4PrimeSineInverseSquareTermInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut suzukiDF6D4PrimeTailIntervalDenominator
    (RationalInterval.scale (1 / ((mode : Rat) ^ 2))
      (suzukiDF6D4FrozenPrimeSineInterval mode))

def suzukiDF6D4PrimeSineSquareInverseSquareTermInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut suzukiDF6D4PrimeTailIntervalDenominator
    (RationalInterval.scale (1 / ((mode : Rat) ^ 2))
      ((suzukiDF6D4FrozenPrimeSineInterval mode).mulCentered
        (suzukiDF6D4FrozenPrimeSineInterval mode)))

def suzukiDF6D4PrimeSineInverseSquareFiniteInterval : RationalInterval :=
  RationalInterval.sum (Finset.range suzukiDF6D4PrimeTailFiniteCount) fun k =>
    suzukiDF6D4PrimeSineInverseSquareTermInterval (601 + k)

def suzukiDF6D4PrimeSineSquareInverseSquareFiniteInterval : RationalInterval :=
  RationalInterval.sum (Finset.range suzukiDF6D4PrimeTailFiniteCount) fun k =>
    suzukiDF6D4PrimeSineSquareInverseSquareTermInterval (601 + k)

theorem suzukiDF6D4PrimeSineInverseSquareFiniteInterval_contains :
    suzukiDF6D4PrimeSineInverseSquareFiniteInterval.Contains
      (∑ k ∈ Finset.range suzukiDF6D4PrimeTailFiniteCount,
        Real.sin (((601 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) /
          (((601 + k : Nat) : Real) ^ 2)) := by
  unfold suzukiDF6D4PrimeSineInverseSquareFiniteInterval
  apply RationalInterval.contains_sum
  intro k hk
  have hklt : k < suzukiDF6D4PrimeTailFiniteCount := Finset.mem_range.mp hk
  have hsine := suzukiDF6D4FrozenPrimeSineInterval_contains
    (601 + k) (by
      unfold suzukiDF6D4PrimeTailFiniteCount at hklt
      omega)
  have hscale := RationalInterval.contains_scale
    (1 / (((601 + k : Nat) : Rat) ^ 2)) hsine
  unfold suzukiDF6D4PrimeSineInverseSquareTermInterval
  apply RationalInterval.contains_roundOut
    (by norm_num [suzukiDF6D4PrimeTailIntervalDenominator])
  convert hscale using 1
  unfold suzukiDF6D4PrimeTailPhase
  norm_num
  push_cast
  ring

theorem suzukiDF6D4PrimeSineSquareInverseSquareFiniteInterval_contains :
    suzukiDF6D4PrimeSineSquareInverseSquareFiniteInterval.Contains
      (∑ k ∈ Finset.range suzukiDF6D4PrimeTailFiniteCount,
        Real.sin (((601 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) ^ 2 /
          (((601 + k : Nat) : Real) ^ 2)) := by
  unfold suzukiDF6D4PrimeSineSquareInverseSquareFiniteInterval
  apply RationalInterval.contains_sum
  intro k hk
  have hklt : k < suzukiDF6D4PrimeTailFiniteCount := Finset.mem_range.mp hk
  have hsine := suzukiDF6D4FrozenPrimeSineInterval_contains
    (601 + k) (by
      unfold suzukiDF6D4PrimeTailFiniteCount at hklt
      omega)
  have hsquare := RationalInterval.contains_mulCentered hsine hsine
  have hscale := RationalInterval.contains_scale
    (1 / (((601 + k : Nat) : Rat) ^ 2)) hsquare
  unfold suzukiDF6D4PrimeSineSquareInverseSquareTermInterval
  apply RationalInterval.contains_roundOut
    (by norm_num [suzukiDF6D4PrimeTailIntervalDenominator])
  convert hscale using 1
  unfold suzukiDF6D4PrimeTailPhase
  norm_num
  push_cast
  ring

def suzukiDF6D4PrimePhaseSineAbsLower : Rat :=
  -(suzukiDF6D4FrozenPrimeSineInterval 1).upper

theorem suzukiDF6D4PrimePhaseSineAbsLower_pos :
    0 < suzukiDF6D4PrimePhaseSineAbsLower := by
  native_decide

private theorem suzukiDF6D4PrimeTailPhase_sine_neg :
    Real.sin suzukiDF6D4PrimeTailPhase < 0 := by
  have hcontains := suzukiDF6D4FrozenPrimeSineInterval_contains 1 (by norm_num)
  have hupper : (suzukiDF6D4FrozenPrimeSineInterval 1).upper < 0 := by
    native_decide
  have hupperReal :
      ((suzukiDF6D4FrozenPrimeSineInterval 1).upper : Real) < 0 := by
    exact_mod_cast hupper
  have hsine : Real.sin suzukiDF6D4PrimeTailPhase ≤
      ((suzukiDF6D4FrozenPrimeSineInterval 1).upper : Real) := by
    convert hcontains.2 using 1
    unfold suzukiDF6D4PrimeTailPhase
    ring
  exact hsine.trans_lt hupperReal

theorem suzukiDF6D4PrimePhaseSineAbsLower_le :
    ((suzukiDF6D4PrimePhaseSineAbsLower : Rat) : Real) ≤
      |Real.sin suzukiDF6D4PrimeTailPhase| := by
  have hcontains := suzukiDF6D4FrozenPrimeSineInterval_contains 1 (by norm_num)
  have hsine : Real.sin suzukiDF6D4PrimeTailPhase ≤
      ((suzukiDF6D4FrozenPrimeSineInterval 1).upper : Real) := by
    convert hcontains.2 using 1
    unfold suzukiDF6D4PrimeTailPhase
    ring
  rw [abs_of_neg suzukiDF6D4PrimeTailPhase_sine_neg]
  unfold suzukiDF6D4PrimePhaseSineAbsLower
  norm_num
  exact hsine

private theorem suzukiDF6D4PrimeTailPhase_half_sine_ne_zero :
    Real.sin (suzukiDF6D4PrimeTailPhase / 2) ≠ 0 := by
  intro hzero
  have hsinZero : Real.sin suzukiDF6D4PrimeTailPhase = 0 := by
    calc
      Real.sin suzukiDF6D4PrimeTailPhase =
          Real.sin (2 * (suzukiDF6D4PrimeTailPhase / 2)) := by ring_nf
      _ = 2 * Real.sin (suzukiDF6D4PrimeTailPhase / 2) *
          Real.cos (suzukiDF6D4PrimeTailPhase / 2) :=
        Real.sin_two_mul _
      _ = 0 := by rw [hzero]; ring
  exact suzukiDF6D4PrimeTailPhase_sine_neg.ne hsinZero

private theorem suzukiDF6D4PrimePhase_half_inverse_abs_le :
    1 / |Real.sin (suzukiDF6D4PrimeTailPhase / 2)| ≤
      2 / (suzukiDF6D4PrimePhaseSineAbsLower : Real) := by
  have hLowerPos : (0 : Real) < suzukiDF6D4PrimePhaseSineAbsLower := by
    exact_mod_cast suzukiDF6D4PrimePhaseSineAbsLower_pos
  have hhalfPos : 0 < |Real.sin (suzukiDF6D4PrimeTailPhase / 2)| :=
    abs_pos.mpr suzukiDF6D4PrimeTailPhase_half_sine_ne_zero
  have hsinDouble :
      Real.sin suzukiDF6D4PrimeTailPhase =
        2 * Real.sin (suzukiDF6D4PrimeTailPhase / 2) *
          Real.cos (suzukiDF6D4PrimeTailPhase / 2) := by
    calc
      Real.sin suzukiDF6D4PrimeTailPhase =
          Real.sin (2 * (suzukiDF6D4PrimeTailPhase / 2)) := by
        congr 1
        ring
      _ = 2 * Real.sin (suzukiDF6D4PrimeTailPhase / 2) *
          Real.cos (suzukiDF6D4PrimeTailPhase / 2) := Real.sin_two_mul _
  have hdouble :
      |Real.sin suzukiDF6D4PrimeTailPhase| ≤
        2 * |Real.sin (suzukiDF6D4PrimeTailPhase / 2)| := by
    calc
      |Real.sin suzukiDF6D4PrimeTailPhase| =
          |2 * Real.sin (suzukiDF6D4PrimeTailPhase / 2) *
            Real.cos (suzukiDF6D4PrimeTailPhase / 2)| := by
        rw [hsinDouble]
      _ = 2 * |Real.sin (suzukiDF6D4PrimeTailPhase / 2)| *
          |Real.cos (suzukiDF6D4PrimeTailPhase / 2)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
      _ ≤ 2 * |Real.sin (suzukiDF6D4PrimeTailPhase / 2)| * 1 := by
        gcongr
        exact Real.abs_cos_le_one _
      _ = 2 * |Real.sin (suzukiDF6D4PrimeTailPhase / 2)| := by ring
  have hhalfLower :
      (suzukiDF6D4PrimePhaseSineAbsLower : Real) / 2 ≤
        |Real.sin (suzukiDF6D4PrimeTailPhase / 2)| := by
    linarith [suzukiDF6D4PrimePhaseSineAbsLower_le, hdouble]
  calc
    1 / |Real.sin (suzukiDF6D4PrimeTailPhase / 2)| ≤
        1 / ((suzukiDF6D4PrimePhaseSineAbsLower : Real) / 2) :=
      one_div_le_one_div_of_le (by positivity) hhalfLower
    _ = 2 / (suzukiDF6D4PrimePhaseSineAbsLower : Real) := by
      field_simp

private theorem suzukiDF6D4PrimePhase_inverse_abs_le :
    1 / |Real.sin suzukiDF6D4PrimeTailPhase| ≤
      1 / (suzukiDF6D4PrimePhaseSineAbsLower : Real) := by
  have hLowerPos : (0 : Real) < suzukiDF6D4PrimePhaseSineAbsLower := by
    exact_mod_cast suzukiDF6D4PrimePhaseSineAbsLower_pos
  exact one_div_le_one_div_of_le hLowerPos
    suzukiDF6D4PrimePhaseSineAbsLower_le

def suzukiDF6D4PrimeSineTailRemainderBound : Rat :=
  (2 / suzukiDF6D4PrimePhaseSineAbsLower) * (1 / (20001 : Rat) ^ 2)

def suzukiDF6D4PrimeSineSquareTailCenteredErrorBound : Rat :=
  (1 / 2) * (1 / suzukiDF6D4PrimePhaseSineAbsLower) *
    (1 / (20001 : Rat) ^ 2)

def suzukiDF6D4PrimeSineTailRemainderInterval : RationalInterval :=
  ⟨-suzukiDF6D4PrimeSineTailRemainderBound,
    suzukiDF6D4PrimeSineTailRemainderBound⟩

def suzukiDF6D4PrimeSineSquareTailRemainderInterval : RationalInterval :=
  (RationalInterval.scale (1 / 2)
      (suzukiDF6D4InverseSquareTailInterval 20000)).add
    ⟨-suzukiDF6D4PrimeSineSquareTailCenteredErrorBound,
      suzukiDF6D4PrimeSineSquareTailCenteredErrorBound⟩

private theorem suzukiDF6D4PrimeSineTailRemainderInterval_contains :
    suzukiDF6D4PrimeSineTailRemainderInterval.Contains
      (∑' k : Nat,
        Real.sin (((20001 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) /
          (((20001 + k : Nat) : Real) ^ 2)) := by
  have hdirichlet := suzukiDF6D4SineInverseSquareTailAbs_le
    suzukiDF6D4PrimeTailPhase
    suzukiDF6D4PrimeTailPhase_half_sine_ne_zero 20000
  have hbound :
      |∑' k : Nat,
        Real.sin (((20001 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) /
          (((20001 + k : Nat) : Real) ^ 2)| ≤
        (suzukiDF6D4PrimeSineTailRemainderBound : Real) := by
    calc
      _ ≤ (1 / |Real.sin (suzukiDF6D4PrimeTailPhase / 2)|) *
          (1 / (((20001 : Nat) : Real) ^ 2)) := by
        simpa only [Nat.reduceAdd] using hdirichlet
      _ ≤ (2 / (suzukiDF6D4PrimePhaseSineAbsLower : Real)) *
          (1 / (((20001 : Nat) : Real) ^ 2)) := by
        exact mul_le_mul_of_nonneg_right
          suzukiDF6D4PrimePhase_half_inverse_abs_le (by positivity)
      _ = (suzukiDF6D4PrimeSineTailRemainderBound : Real) := by
        unfold suzukiDF6D4PrimeSineTailRemainderBound
        norm_num
  unfold suzukiDF6D4PrimeSineTailRemainderInterval RationalInterval.Contains
  norm_num
  simpa only [Nat.cast_add, Nat.cast_ofNat] using (abs_le.mp hbound)

private theorem suzukiDF6D4PrimeSineSquareTailRemainderInterval_contains :
    suzukiDF6D4PrimeSineSquareTailRemainderInterval.Contains
      (∑' k : Nat,
        Real.sin (((20001 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) ^ 2 /
          (((20001 + k : Nat) : Real) ^ 2)) := by
  have hcenter := suzukiDF6D4SineSquareInverseSquareTailCenteredAbs_le
    suzukiDF6D4PrimeTailPhase
    suzukiDF6D4PrimeTailPhase_sine_neg.ne 20000
  let center : Real := (1 / 2) * suzukiDF6D4InverseSquareTail 20000
  let tail : Real := ∑' k : Nat,
    Real.sin (((20001 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) ^ 2 /
      (((20001 + k : Nat) : Real) ^ 2)
  have herror : |tail - center| ≤
      (suzukiDF6D4PrimeSineSquareTailCenteredErrorBound : Real) := by
    calc
      _ ≤ (1 / 2) * ((1 / |Real.sin suzukiDF6D4PrimeTailPhase|) *
          (1 / (((20001 : Nat) : Real) ^ 2))) := by
        simpa only [tail, center, Nat.reduceAdd] using hcenter
      _ ≤ (1 / 2) *
          ((1 / (suzukiDF6D4PrimePhaseSineAbsLower : Real)) *
            (1 / (((20001 : Nat) : Real) ^ 2))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right suzukiDF6D4PrimePhase_inverse_abs_le
            (by positivity)) (by norm_num)
      _ = (suzukiDF6D4PrimeSineSquareTailCenteredErrorBound : Real) := by
        unfold suzukiDF6D4PrimeSineSquareTailCenteredErrorBound
        norm_num
        ring
  have hcenterInterval := RationalInterval.contains_scale (1 / 2)
    (suzukiDF6D4InverseSquareTailInterval_contains 20000)
  have herrorInterval :
      (⟨-suzukiDF6D4PrimeSineSquareTailCenteredErrorBound,
          suzukiDF6D4PrimeSineSquareTailCenteredErrorBound⟩ :
        RationalInterval).Contains (tail - center) := by
    unfold RationalInterval.Contains
    norm_num
    constructor <;> linarith [abs_le.mp herror |>.1, abs_le.mp herror |>.2]
  have hadd := RationalInterval.contains_add hcenterInterval herrorInterval
  unfold suzukiDF6D4PrimeSineSquareTailRemainderInterval
  convert hadd using 1
  dsimp only [tail, center]
  ring

def suzukiDF6D4PrimeSineInverseSquareTailInterval : RationalInterval :=
  RationalInterval.roundOut suzukiDF6D4PrimeTailIntervalDenominator
    (suzukiDF6D4PrimeSineInverseSquareFiniteInterval.add
      suzukiDF6D4PrimeSineTailRemainderInterval)

def suzukiDF6D4PrimeSineSquareInverseSquareTailInterval : RationalInterval :=
  RationalInterval.roundOut suzukiDF6D4PrimeTailIntervalDenominator
    (suzukiDF6D4PrimeSineSquareInverseSquareFiniteInterval.add
      suzukiDF6D4PrimeSineSquareTailRemainderInterval)

theorem suzukiDF6D4PrimeSineInverseSquareTailInterval_contains :
    suzukiDF6D4PrimeSineInverseSquareTailInterval.Contains
      suzukiDF6D4PrimeSineInverseSquareTail := by
  have hfinite := suzukiDF6D4PrimeSineInverseSquareFiniteInterval_contains
  have hremainder := suzukiDF6D4PrimeSineTailRemainderInterval_contains
  have hadd := RationalInterval.contains_add hfinite hremainder
  have hsum := suzukiDF6D4PrimeSineInverseSquare_summable
    |>.sum_add_tsum_nat_add suzukiDF6D4PrimeTailFiniteCount
  unfold suzukiDF6D4PrimeSineInverseSquareTailInterval
  apply RationalInterval.contains_roundOut
    (by norm_num [suzukiDF6D4PrimeTailIntervalDenominator])
  convert hadd using 1
  unfold suzukiDF6D4PrimeSineInverseSquareTail
  rw [← hsum]
  unfold suzukiDF6D4PrimeTailFiniteCount
  congr 1
  apply tsum_congr
  intro k
  have hindex : 601 + (k + 19400) = 20001 + k := by omega
  rw [hindex]

theorem suzukiDF6D4PrimeSineSquareInverseSquareTailInterval_contains :
    suzukiDF6D4PrimeSineSquareInverseSquareTailInterval.Contains
      suzukiDF6D4PrimeSineSquareInverseSquareTail := by
  have hfinite := suzukiDF6D4PrimeSineSquareInverseSquareFiniteInterval_contains
  have hremainder := suzukiDF6D4PrimeSineSquareTailRemainderInterval_contains
  have hadd := RationalInterval.contains_add hfinite hremainder
  have hsum := suzukiDF6D4PrimeSineSquareInverseSquare_summable
    |>.sum_add_tsum_nat_add suzukiDF6D4PrimeTailFiniteCount
  unfold suzukiDF6D4PrimeSineSquareInverseSquareTailInterval
  apply RationalInterval.contains_roundOut
    (by norm_num [suzukiDF6D4PrimeTailIntervalDenominator])
  convert hadd using 1
  unfold suzukiDF6D4PrimeSineSquareInverseSquareTail
  rw [← hsum]
  unfold suzukiDF6D4PrimeTailFiniteCount
  congr 1
  apply tsum_congr
  intro k
  have hindex : 601 + (k + 19400) = 20001 + k := by omega
  rw [hindex]

/-! ## Compact frozen endpoints

The definitions above are the proof-producing computation.  The matrix layer
uses these compact outward roundings so that evaluating a `45 × 45` grid does
not repeat the 19,400-term audit at every entry. -/

def suzukiDF6D4FrozenPrimeSineInverseSquareTailInterval :
    RationalInterval :=
  ⟨(-2447392 / 1000000000000 : Rat),
    (-2436677 / 1000000000000 : Rat)⟩

def suzukiDF6D4FrozenPrimeSineSquareInverseSquareTailInterval :
    RationalInterval :=
  ⟨(83276267 / 100000000000 : Rat),
    (83276536 / 100000000000 : Rat)⟩

set_option maxHeartbeats 0 in
private theorem suzukiDF6D4FrozenPrimeTailIntervals_admit :
    let sine := suzukiDF6D4PrimeSineInverseSquareTailInterval
    let sineSq := suzukiDF6D4PrimeSineSquareInverseSquareTailInterval
    suzukiDF6D4FrozenPrimeSineInverseSquareTailInterval.lower ≤ sine.lower ∧
      sine.upper ≤
        suzukiDF6D4FrozenPrimeSineInverseSquareTailInterval.upper ∧
      suzukiDF6D4FrozenPrimeSineSquareInverseSquareTailInterval.lower ≤
        sineSq.lower ∧
      sineSq.upper ≤
        suzukiDF6D4FrozenPrimeSineSquareInverseSquareTailInterval.upper := by
  native_decide

theorem suzukiDF6D4FrozenPrimeSineInverseSquareTailInterval_contains :
    suzukiDF6D4FrozenPrimeSineInverseSquareTailInterval.Contains
      suzukiDF6D4PrimeSineInverseSquareTail := by
  have h := suzukiDF6D4FrozenPrimeTailIntervals_admit
  exact RationalInterval.contains_of_widen
    h.1 h.2.1
    suzukiDF6D4PrimeSineInverseSquareTailInterval_contains

theorem suzukiDF6D4FrozenPrimeSineSquareInverseSquareTailInterval_contains :
    suzukiDF6D4FrozenPrimeSineSquareInverseSquareTailInterval.Contains
      suzukiDF6D4PrimeSineSquareInverseSquareTail := by
  have h := suzukiDF6D4FrozenPrimeTailIntervals_admit
  exact RationalInterval.contains_of_widen
    h.2.2.1 h.2.2.2
    suzukiDF6D4PrimeSineSquareInverseSquareTailInterval_contains

end

end RiemannHypothesisProject.Experiments.M100
