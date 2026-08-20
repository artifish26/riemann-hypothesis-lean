import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointConstantEnclosures

/-!
# Fine endpoint constant enclosures for M100-DF6D4

The convolution checker needs substantially more precision than the coarse
route-level endpoint brackets.  This module refines `log 2`, `sqrt 2`, and the
frozen endpoint `a*` by proved rational inequalities; no decimal evaluator is
trusted by the Lean admission path.
-/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxHeartbeats 1000000

def fineLogTwoInterval : RationalInterval :=
  ⟨693147180559945309 / 1000000000000000000,
    693147180559945310 / 1000000000000000000⟩

def fineSqrtTwoInterval : RationalInterval :=
  ⟨1414213562373095048 / 1000000000000000000,
    1414213562373095049 / 1000000000000000000⟩

def fineAStarInterval : RationalInterval :=
  ⟨42867814670054956 / 100000000000000000,
    42867814670054957 / 100000000000000000⟩

theorem fineLogTwoInterval_contains :
    fineLogTwoInterval.Contains (Real.log 2) := by
  have hL := Real.sum_range_le_log_div
    (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 24
  have hU := Real.log_div_le_sum_range_add
    (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 24
  unfold fineLogTwoInterval RationalInterval.Contains
  norm_num [Finset.sum_range_succ] at hL hU ⊢
  constructor <;> linarith

theorem fineSqrtTwoInterval_contains :
    fineSqrtTwoInterval.Contains (Real.sqrt 2) := by
  unfold fineSqrtTwoInterval RationalInterval.Contains
  norm_num
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · have hlowerSq :
        (1414213562373095048 / 1000000000000000000 : Real) ^ 2 < 2 := by
      norm_num
    nlinarith
  · have hupperSq :
        2 < (1414213562373095049 / 1000000000000000000 : Real) ^ 2 := by
      norm_num
    nlinarith

private theorem exp_product_upper_lower :
    (375214227246481772 / 1000000000000000000 : Real) ≤
      Real.exp (-980258143468547193 / 1000000000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-980258143468547193 / 1000000000000000000 : Real))
    (n := 24) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem exp_product_lower_upper :
    Real.exp (-980258143468547190 / 1000000000000000000 : Real) ≤
      (375214227246481775 / 1000000000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-980258143468547190 / 1000000000000000000 : Real))
    (n := 24) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem fineAStarInterval_contains :
    fineAStarInterval.Contains suzukiProjectAStar := by
  have hL := fineLogTwoInterval_contains
  have hS := fineSqrtTwoInterval_contains
  unfold fineLogTwoInterval RationalInterval.Contains at hL
  unfold fineSqrtTwoInterval RationalInterval.Contains at hS
  norm_num at hL hS
  have hLLower :
      (693147180559945309 / 1000000000000000000 : Real) ≤ Real.log 2 := by
    norm_num
    exact hL.1
  have hLUpper :
      Real.log 2 ≤ (693147180559945310 / 1000000000000000000 : Real) := by
    norm_num
    exact hL.2
  have hSLower :
      (1414213562373095048 / 1000000000000000000 : Real) ≤ Real.sqrt 2 := by
    norm_num
    exact hS.1
  have hSUpper :
      Real.sqrt 2 ≤ (1414213562373095049 / 1000000000000000000 : Real) := by
    norm_num
    exact hS.2
  let y : Real := -(Real.sqrt 2 * Real.log 2)
  have hprodLowerBase :
      (1414213562373095048 / 1000000000000000000 : Real) *
          (693147180559945309 / 1000000000000000000 : Real) ≤
        Real.sqrt 2 * Real.log 2 :=
    mul_le_mul hSLower hLLower (by norm_num) (Real.sqrt_nonneg 2)
  have hprodLower :
      (980258143468547190 / 1000000000000000000 : Real) ≤
        Real.sqrt 2 * Real.log 2 := by
    calc
      (980258143468547190 / 1000000000000000000 : Real) ≤
          (1414213562373095048 / 1000000000000000000 : Real) *
            (693147180559945309 / 1000000000000000000 : Real) := by norm_num
      _ ≤ Real.sqrt 2 * Real.log 2 := hprodLowerBase
  have hprodUpperBase :
      Real.sqrt 2 * Real.log 2 ≤
        (1414213562373095049 / 1000000000000000000 : Real) *
          (693147180559945310 / 1000000000000000000 : Real) :=
    mul_le_mul hSUpper hLUpper (Real.log_pos (by norm_num)).le (by norm_num)
  have hprodUpper :
      Real.sqrt 2 * Real.log 2 ≤
        (980258143468547193 / 1000000000000000000 : Real) := by
    calc
      Real.sqrt 2 * Real.log 2 ≤
          (1414213562373095049 / 1000000000000000000 : Real) *
            (693147180559945310 / 1000000000000000000 : Real) := hprodUpperBase
      _ ≤ (980258143468547193 / 1000000000000000000 : Real) := by norm_num
  have hyLower :
      (-980258143468547193 / 1000000000000000000 : Real) ≤ y := by
    dsimp only [y]
    linarith
  have hyUpper :
      y ≤ (-980258143468547190 / 1000000000000000000 : Real) := by
    dsimp only [y]
    linarith
  have hExpLower :
      (375214227246481772 / 1000000000000000000 : Real) ≤ Real.exp y :=
    exp_product_upper_lower.trans (Real.exp_le_exp.mpr hyLower)
  have hExpUpper :
      Real.exp y ≤ (375214227246481775 / 1000000000000000000 : Real) :=
    (Real.exp_le_exp.mpr hyUpper).trans exp_product_lower_upper
  have hExpSquare :
      Real.exp (-2 * Real.sqrt 2 * Real.log 2) =
        Real.exp y * Real.exp y := by
    rw [show -2 * Real.sqrt 2 * Real.log 2 = y + y by
      dsimp only [y]
      ring, Real.exp_add]
  have hDoubleExpLower :
      (375214227246481772 / 1000000000000000000 : Real) ^ 2 ≤
        Real.exp (-2 * Real.sqrt 2 * Real.log 2) := by
    rw [hExpSquare]
    nlinarith [Real.exp_pos y]
  have hDoubleExpUpper :
      Real.exp (-2 * Real.sqrt 2 * Real.log 2) ≤
        (375214227246481775 / 1000000000000000000 : Real) ^ 2 := by
    rw [hExpSquare]
    nlinarith [Real.exp_pos y]
  let z : Real :=
    Real.log 2 ^ 2 + 4 * Real.exp (-2 * Real.sqrt 2 * Real.log 2)
  have hzNonneg : 0 ≤ z := by
    dsimp only [z]
    positivity
  have hzSqrt : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hzNonneg
  have hzSqrtNonneg : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
  have hlowerNumerical :
      4 * (42867814670054956 / 100000000000000000 : Real) ^ 2 -
          2 * (42867814670054956 / 100000000000000000 : Real) *
            (693147180559945309 / 1000000000000000000 : Real) ≤
        (375214227246481772 / 1000000000000000000 : Real) ^ 2 := by
    norm_num
  have hlowerAlgebra :
      4 * (42867814670054956 / 100000000000000000 : Real) ^ 2 -
          2 * (42867814670054956 / 100000000000000000 : Real) * Real.log 2 ≤
        Real.exp (-2 * Real.sqrt 2 * Real.log 2) := by
    nlinarith
  have hlowerSquare :
      (4 * (42867814670054956 / 100000000000000000 : Real) - Real.log 2) ^ 2 ≤ z := by
    dsimp only [z]
    nlinarith
  have hlowerRoot :
      4 * (42867814670054956 / 100000000000000000 : Real) - Real.log 2 ≤
        Real.sqrt z := by
    have hleftNonneg :
        0 ≤ 4 * (42867814670054956 / 100000000000000000 : Real) - Real.log 2 := by
      nlinarith
    nlinarith
  have hupperNumerical :
      (375214227246481775 / 1000000000000000000 : Real) ^ 2 ≤
        4 * (42867814670054957 / 100000000000000000 : Real) ^ 2 -
          2 * (42867814670054957 / 100000000000000000 : Real) *
            (693147180559945310 / 1000000000000000000 : Real) := by
    norm_num
  have hupperAlgebra :
      Real.exp (-2 * Real.sqrt 2 * Real.log 2) ≤
        4 * (42867814670054957 / 100000000000000000 : Real) ^ 2 -
          2 * (42867814670054957 / 100000000000000000 : Real) * Real.log 2 := by
    nlinarith
  have hupperSquare :
      z ≤ (4 * (42867814670054957 / 100000000000000000 : Real) - Real.log 2) ^ 2 := by
    dsimp only [z]
    nlinarith
  have hupperRoot :
      Real.sqrt z ≤
        4 * (42867814670054957 / 100000000000000000 : Real) - Real.log 2 := by
    have hrightNonneg :
        0 ≤ 4 * (42867814670054957 / 100000000000000000 : Real) - Real.log 2 := by
      nlinarith
    nlinarith
  unfold fineAStarInterval RationalInterval.Contains
  unfold suzukiProjectAStar
  change
    ((42867814670054956 / 100000000000000000 : Rat) : Real) ≤
        (Real.log 2 + Real.sqrt z) / 4 ∧
      (Real.log 2 + Real.sqrt z) / 4 ≤
        ((42867814670054957 / 100000000000000000 : Rat) : Real)
  norm_num
  constructor <;> linarith

/-- Fine enclosure of `exp (-a*)`, used by the 128-term restoration powers
and by the endpoint pole/cosh contribution. -/
def fineExpNegAStarInterval : RationalInterval :=
  ⟨651369540883008815 / 1000000000000000000,
    651369540883008823 / 1000000000000000000⟩

private theorem exp_neg_fineA_upper_lower :
    (651369540883008815 / 1000000000000000000 : Real) ≤
      Real.exp (-42867814670054957 / 100000000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-42867814670054957 / 100000000000000000 : Real))
    (n := 22) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem exp_neg_fineA_lower_upper :
    Real.exp (-42867814670054956 / 100000000000000000 : Real) ≤
      (651369540883008823 / 1000000000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-42867814670054956 / 100000000000000000 : Real))
    (n := 22) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem fineExpNegAStarInterval_contains :
    fineExpNegAStarInterval.Contains (Real.exp (-suzukiProjectAStar)) := by
  have hA := fineAStarInterval_contains
  unfold fineAStarInterval RationalInterval.Contains at hA
  norm_num at hA
  have hNegLower :
      (-42867814670054957 / 100000000000000000 : Real) ≤
        -suzukiProjectAStar := by
    linarith
  have hNegUpper :
      -suzukiProjectAStar ≤
        (-42867814670054956 / 100000000000000000 : Real) := by
    linarith
  unfold fineExpNegAStarInterval RationalInterval.Contains
  norm_num
  constructor
  · have h := exp_neg_fineA_upper_lower.trans
        (Real.exp_le_exp.mpr hNegLower)
    norm_num at h ⊢
    exact h
  · have h := (Real.exp_le_exp.mpr hNegUpper).trans
        exp_neg_fineA_lower_upper
    norm_num at h ⊢
    exact h

/-! ## Fine Euler enclosure -/

def fineEulerInterval : RationalInterval :=
  ⟨577215664 / 1000000000, 577215666 / 1000000000⟩

private theorem fineEulerPartialRat_bounds :
    (577215664 / 1000000000 : Rat) +
          14 * (693147180559945310 / 1000000000000000000 : Rat) +
          1 / (2 * 16384 : Rat) ≤
        harmonic 16384 ∧
      harmonic 16384 ≤
        (577215666 / 1000000000 : Rat) +
          14 * (693147180559945309 / 1000000000000000000 : Rat) +
          1 / (2 * 16384 + 1 : Rat) := by
  native_decide

theorem fineEulerInterval_contains :
    fineEulerInterval.Contains Real.eulerMascheroniConstant := by
  have hcorrected := suzukiDF6D4_euler_corrected_bounds 16384 (by norm_num)
  have hlogTwo := fineLogTwoInterval_contains
  have hrat := fineEulerPartialRat_bounds
  have hlogPower : Real.log (16384 : Real) = 14 * Real.log 2 := by
    rw [show (16384 : Real) = 2 ^ 14 by norm_num, Real.log_pow]
    norm_num
  have hcast16384 : ((16384 : Nat) : Real) = (16384 : Real) := by
    norm_num
  rw [hcast16384, hlogPower] at hcorrected
  unfold fineLogTwoInterval RationalInterval.Contains at hlogTwo
  unfold fineEulerInterval RationalInterval.Contains
  constructor
  · have hratLower := (Rat.cast_le (K := Real)).2 hrat.1
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat] at hratLower ⊢
    have hharmonic : ((harmonic 16384 : Rat) : Real) =
        (harmonic 16384 : Real) := rfl
    rw [hharmonic] at hratLower
    linarith
  · have hratUpper := (Rat.cast_le (K := Real)).2 hrat.2
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat] at hratUpper ⊢
    have hharmonic : ((harmonic 16384 : Rat) : Real) =
        (harmonic 16384 : Real) := rfl
    rw [hharmonic] at hratUpper
    linarith

/-! ## Logarithmic scalar used by every diagonal entry -/

/-- Fine enclosure of `log (4 * π)`.  The proof compares rational Taylor
bounds for the exponential with the already proved 20-decimal enclosure of
`π`, so no decimal logarithm evaluator enters the certificate. -/
def fineLogFourPiInterval : RationalInterval :=
  ⟨2531024246969280 / 1000000000000000,
    2531024246969300 / 1000000000000000⟩

private theorem exp_logFourPi_quarter_lower_upper :
    Real.exp (2531024246969280 / 4000000000000000 : Real) ≤
      (1882792527553425 / 1000000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (2531024246969280 / 4000000000000000 : Real))
    (n := 32) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem exp_logFourPi_quarter_upper_lower :
    (1882792527553433 / 1000000000000000 : Real) ≤
      Real.exp (2531024246969300 / 4000000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (2531024246969300 / 4000000000000000 : Real))
    (n := 32) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem exp_logFourPi_lower_le :
    Real.exp (2531024246969280 / 1000000000000000 : Real) ≤
      4 * (314159265358979323846 / 100000000000000000000 : Real) := by
  rw [show (2531024246969280 / 1000000000000000 : Real) =
      (4 : Nat) * (2531024246969280 / 4000000000000000 : Real) by norm_num,
    Real.exp_nat_mul]
  calc
    Real.exp (2531024246969280 / 4000000000000000 : Real) ^ 4 ≤
        (1882792527553425 / 1000000000000000 : Real) ^ 4 :=
      pow_le_pow_left₀ (Real.exp_pos _).le
        exp_logFourPi_quarter_lower_upper 4
    _ ≤ 4 * (314159265358979323846 / 100000000000000000000 : Real) := by
      norm_num

private theorem exp_logFourPi_upper_ge :
    4 * (314159265358979323847 / 100000000000000000000 : Real) ≤
      Real.exp (2531024246969300 / 1000000000000000 : Real) := by
  rw [show (2531024246969300 / 1000000000000000 : Real) =
      (4 : Nat) * (2531024246969300 / 4000000000000000 : Real) by norm_num,
    Real.exp_nat_mul]
  calc
    4 * (314159265358979323847 / 100000000000000000000 : Real) ≤
        (1882792527553433 / 1000000000000000 : Real) ^ 4 := by
      norm_num
    _ ≤ Real.exp (2531024246969300 / 4000000000000000 : Real) ^ 4 :=
      pow_le_pow_left₀ (by norm_num)
        exp_logFourPi_quarter_upper_lower 4

theorem fineLogFourPiInterval_contains :
    fineLogFourPiInterval.Contains (Real.log (4 * Real.pi)) := by
  have hPi := suzukiDF6D4PiInterval_contains
  have hPiLower :
      (314159265358979323846 / 100000000000000000000 : Real) ≤
        Real.pi := by
    simpa [suzukiDF6D4PiInterval, RationalInterval.Contains] using hPi.1
  have hPiUpper :
      Real.pi ≤
        (314159265358979323847 / 100000000000000000000 : Real) := by
    simpa [suzukiDF6D4PiInterval, RationalInterval.Contains] using hPi.2
  have hArgPos : 0 < 4 * Real.pi := by positivity
  have hLowerExp :
      Real.exp (2531024246969280 / 1000000000000000 : Real) ≤
        4 * Real.pi := by
    exact exp_logFourPi_lower_le.trans
      (mul_le_mul_of_nonneg_left hPiLower (by norm_num))
  have hUpperExp :
      4 * Real.pi ≤
        Real.exp (2531024246969300 / 1000000000000000 : Real) := by
    exact (mul_le_mul_of_nonneg_left hPiUpper (by norm_num)).trans
      exp_logFourPi_upper_ge
  unfold fineLogFourPiInterval RationalInterval.Contains
  norm_num at hLowerExp hUpperExp ⊢
  constructor
  · apply Real.exp_le_exp.mp
    simpa [Real.exp_log hArgPos] using hLowerExp
  · apply Real.exp_le_exp.mp
    simpa [Real.exp_log hArgPos] using hUpperExp

end RiemannHypothesisProject.Experiments.M100
