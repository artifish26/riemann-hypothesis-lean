import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import RiemannHypothesisProject.Experiments.M100.RationalIntervalArithmetic

/-!
# Rational Taylor enclosures for sine and cosine

These exact-rational evaluators are specialized to nonnegative arguments at
most one.  Alternating-series error bounds make every omitted remainder
explicit; no floating-point trigonometric evaluation is trusted.
-/

namespace RiemannHypothesisProject.Experiments.M100

open Filter

set_option maxHeartbeats 1000000

private theorem sineTaylorMagnitude_antitone
    {x : Real} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : Nat =>
      x ^ (2 * n + 1) / ((2 * n + 1).factorial : Real)) := by
  intro n m hnm
  apply div_le_div₀
  · positivity
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · positivity
  · exact_mod_cast Nat.factorial_le (by omega : 2 * n + 1 ≤ 2 * m + 1)

private theorem cosineTaylorMagnitude_antitone
    {x : Real} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : Nat =>
      x ^ (2 * n) / ((2 * n).factorial : Real)) := by
  intro n m hnm
  apply div_le_div₀
  · positivity
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · positivity
  · exact_mod_cast Nat.factorial_le (by omega : 2 * n ≤ 2 * m)

theorem real_sine_taylor_error_bound
    (terms : Nat) {x : Real} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sin x -
        ∑ n ∈ Finset.range terms,
          (-1 : Real) ^ n *
            (x ^ (2 * n + 1) / ((2 * n + 1).factorial : Real))| ≤
      x ^ (2 * terms + 1) / ((2 * terms + 1).factorial : Real) := by
  let f : Nat → Real := fun n =>
    x ^ (2 * n + 1) / ((2 * n + 1).factorial : Real)
  have h := alternating_series_error_bound f
    (sineTaylorMagnitude_antitone hx0 hx1)
    (Real.hasSum_sinh x).summable terms
  have hsum :
      (∑' n : Nat, (-1 : Real) ^ n * f n) = Real.sin x :=
    by simpa only [f, mul_div_assoc] using (Real.hasSum_sin x).tsum_eq
  rw [hsum] at h
  exact h

theorem real_cosine_taylor_error_bound
    (terms : Nat) {x : Real} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.cos x -
        ∑ n ∈ Finset.range terms,
          (-1 : Real) ^ n *
            (x ^ (2 * n) / ((2 * n).factorial : Real))| ≤
      x ^ (2 * terms) / ((2 * terms).factorial : Real) := by
  let f : Nat → Real := fun n =>
    x ^ (2 * n) / ((2 * n).factorial : Real)
  have h := alternating_series_error_bound f
    (cosineTaylorMagnitude_antitone hx0 hx1)
    (Real.hasSum_cosh x).summable terms
  have hsum :
      (∑' n : Nat, (-1 : Real) ^ n * f n) = Real.cos x :=
    by simpa only [f, mul_div_assoc] using (Real.hasSum_cos x).tsum_eq
  rw [hsum] at h
  exact h

namespace RationalInterval

def sineTaylorCoefficient (n : Nat) : Rat :=
  (-1 : Rat) ^ n / (2 * n + 1).factorial

def cosineTaylorCoefficient (n : Nat) : Rat :=
  (-1 : Rat) ^ n / (2 * n).factorial

/-- Exact interval evaluation of the first `terms` sine-series terms. -/
def sineTaylorPartial : Nat → RationalInterval → RationalInterval
  | 0, _ => point 0
  | terms + 1, I =>
      (sineTaylorPartial terms I).add
        (scale (sineTaylorCoefficient terms)
          (I.powNonneg (2 * terms + 1)))

/-- Exact interval evaluation of the first `terms` cosine-series terms. -/
def cosineTaylorPartial : Nat → RationalInterval → RationalInterval
  | 0, _ => point 0
  | terms + 1, I =>
      (cosineTaylorPartial terms I).add
        (scale (cosineTaylorCoefficient terms)
          (I.powNonneg (2 * terms)))

theorem contains_sineTaylorPartial
    (terms : Nat) {I : RationalInterval} {x : Real}
    (hI0 : 0 ≤ I.lower) (hx : I.Contains x) :
    (sineTaylorPartial terms I).Contains
      (∑ n ∈ Finset.range terms,
        (-1 : Real) ^ n *
          (x ^ (2 * n + 1) / ((2 * n + 1).factorial : Real))) := by
  induction terms with
  | zero =>
      simpa [sineTaylorPartial] using contains_point 0
  | succ terms ih =>
      rw [Finset.sum_range_succ]
      have hPow := contains_powNonneg (2 * terms + 1) hI0 hx
      have hScale := contains_scale (sineTaylorCoefficient terms) hPow
      have hTerm :
          (scale (sineTaylorCoefficient terms)
            (I.powNonneg (2 * terms + 1))).Contains
          ((-1 : Real) ^ terms *
            (x ^ (2 * terms + 1) /
              ((2 * terms + 1).factorial : Real))) := by
        convert hScale using 1
        unfold sineTaylorCoefficient
        norm_num
        push_cast
        ring
      exact contains_add ih hTerm

theorem contains_cosineTaylorPartial
    (terms : Nat) {I : RationalInterval} {x : Real}
    (hI0 : 0 ≤ I.lower) (hx : I.Contains x) :
    (cosineTaylorPartial terms I).Contains
      (∑ n ∈ Finset.range terms,
        (-1 : Real) ^ n *
          (x ^ (2 * n) / ((2 * n).factorial : Real))) := by
  induction terms with
  | zero =>
      simpa [cosineTaylorPartial] using contains_point 0
  | succ terms ih =>
      rw [Finset.sum_range_succ]
      have hPow := contains_powNonneg (2 * terms) hI0 hx
      have hScale := contains_scale (cosineTaylorCoefficient terms) hPow
      have hTerm :
          (scale (cosineTaylorCoefficient terms)
            (I.powNonneg (2 * terms))).Contains
          ((-1 : Real) ^ terms *
            (x ^ (2 * terms) /
              ((2 * terms).factorial : Real))) := by
        convert hScale using 1
        unfold cosineTaylorCoefficient
        norm_num
        push_cast
        ring
      exact contains_add ih hTerm

def symmetricError (q : Rat) : RationalInterval := ⟨-q, q⟩

def sineTaylorError (terms : Nat) (I : RationalInterval) : Rat :=
  I.upper ^ (2 * terms + 1) / (2 * terms + 1).factorial

def cosineTaylorError (terms : Nat) (I : RationalInterval) : Rat :=
  I.upper ^ (2 * terms) / (2 * terms).factorial

/-- Complete sine enclosure from a finite alternating Taylor sum. -/
def sineTaylor (terms : Nat) (I : RationalInterval) : RationalInterval :=
  (sineTaylorPartial terms I).add
    (symmetricError (sineTaylorError terms I))

/-- Complete cosine enclosure from a finite alternating Taylor sum. -/
def cosineTaylor (terms : Nat) (I : RationalInterval) : RationalInterval :=
  (cosineTaylorPartial terms I).add
    (symmetricError (cosineTaylorError terms I))

theorem contains_sineTaylor
    (terms : Nat) {I : RationalInterval} {x : Real}
    (hI0 : 0 ≤ I.lower) (hI1 : I.upper ≤ 1)
    (hx : I.Contains x) :
    (sineTaylor terms I).Contains (Real.sin x) := by
  have hLowerReal : (0 : Real) ≤ (I.lower : Real) := by exact_mod_cast hI0
  have hUpperReal : (I.upper : Real) ≤ 1 := by exact_mod_cast hI1
  have hx0 : 0 ≤ x := hLowerReal.trans hx.1
  have hx1 : x ≤ 1 := hx.2.trans hUpperReal
  let P : Real := ∑ n ∈ Finset.range terms,
    (-1 : Real) ^ n *
      (x ^ (2 * n + 1) / ((2 * n + 1).factorial : Real))
  have hP := contains_sineTaylorPartial terms hI0 hx
  have hErr := real_sine_taylor_error_bound terms hx0 hx1
  have hPow : x ^ (2 * terms + 1) ≤
      (I.upper : Real) ^ (2 * terms + 1) := by
    exact pow_le_pow_left₀ hx0 hx.2 _
  have hFactorialPos : (0 : Real) < (2 * terms + 1).factorial := by positivity
  have hErrUpper :
      x ^ (2 * terms + 1) / ((2 * terms + 1).factorial : Real) ≤
        ((sineTaylorError terms I : Rat) : Real) := by
    unfold sineTaylorError
    norm_num
    exact div_le_div_of_nonneg_right hPow hFactorialPos.le
  have hSymmetric :
      (symmetricError (sineTaylorError terms I)).Contains
        (Real.sin x - P) := by
    unfold symmetricError RationalInterval.Contains
    norm_num
    rw [abs_le] at hErr
    constructor <;> linarith
  unfold sineTaylor
  convert contains_add hP hSymmetric using 1
  dsimp only [P]
  ring

theorem contains_cosineTaylor
    (terms : Nat) {I : RationalInterval} {x : Real}
    (hI0 : 0 ≤ I.lower) (hI1 : I.upper ≤ 1)
    (hx : I.Contains x) :
    (cosineTaylor terms I).Contains (Real.cos x) := by
  have hLowerReal : (0 : Real) ≤ (I.lower : Real) := by exact_mod_cast hI0
  have hUpperReal : (I.upper : Real) ≤ 1 := by exact_mod_cast hI1
  have hx0 : 0 ≤ x := hLowerReal.trans hx.1
  have hx1 : x ≤ 1 := hx.2.trans hUpperReal
  let P : Real := ∑ n ∈ Finset.range terms,
    (-1 : Real) ^ n *
      (x ^ (2 * n) / ((2 * n).factorial : Real))
  have hP := contains_cosineTaylorPartial terms hI0 hx
  have hErr := real_cosine_taylor_error_bound terms hx0 hx1
  have hPow : x ^ (2 * terms) ≤ (I.upper : Real) ^ (2 * terms) := by
    exact pow_le_pow_left₀ hx0 hx.2 _
  have hFactorialPos : (0 : Real) < (2 * terms).factorial := by positivity
  have hErrUpper :
      x ^ (2 * terms) / ((2 * terms).factorial : Real) ≤
        ((cosineTaylorError terms I : Rat) : Real) := by
    unfold cosineTaylorError
    norm_num
    exact div_le_div_of_nonneg_right hPow hFactorialPos.le
  have hSymmetric :
      (symmetricError (cosineTaylorError terms I)).Contains
        (Real.cos x - P) := by
    unfold symmetricError RationalInterval.Contains
    norm_num
    rw [abs_le] at hErr
    constructor <;> linarith
  unfold cosineTaylor
  convert contains_add hP hSymmetric using 1
  dsimp only [P]
  ring

end RationalInterval

end RiemannHypothesisProject.Experiments.M100
