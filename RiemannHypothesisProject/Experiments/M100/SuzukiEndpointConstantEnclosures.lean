import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RiemannHypothesisProject.Experiments.M100.RationalIntervalArithmetic
import RiemannHypothesisProject.Experiments.M100.SuzukiProjectFormNormalization

/-!
# Elementary constant enclosures for M100-DF6D4

These are the first analytic inputs to the endpoint-entry checker.  The bounds
come from Mathlib's proved exponential/logarithm and pi estimates, plus an
exact squared-rational check for `sqrt 2` and exact rational partial sums with
proved analytic remainders for the Euler-Mascheroni constant, Catalan's
constant, and `zeta(3)`; no decimal evaluator is trusted.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open Filter RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def suzukiDF6D4LogTwoInterval : RationalInterval :=
  ⟨69314718055994 / 100000000000000,
    69314718055995 / 100000000000000⟩

def suzukiDF6D4PiInterval : RationalInterval :=
  ⟨314159265358979323846 / 100000000000000000000,
    314159265358979323847 / 100000000000000000000⟩

def suzukiDF6D4SqrtTwoInterval : RationalInterval :=
  ⟨141421356237309 / 100000000000000,
    141421356237310 / 100000000000000⟩

def suzukiDF6D4EulerInterval : RationalInterval :=
  ⟨57721566 / 100000000, 57721567 / 100000000⟩

def suzukiDF6D4AStarInterval : RationalInterval :=
  ⟨4286781467005 / 10000000000000,
    4286781467006 / 10000000000000⟩

/-- Frozen enclosure of `exp (-a*)`, used to turn every restoration
exponential into a nonnegative rational interval power. -/
def suzukiDF6D4ExpNegAStarInterval : RationalInterval :=
  ⟨65136954088297 / 100000000000000,
    65136954088305 / 100000000000000⟩

theorem suzukiDF6D4LogTwoInterval_contains :
    suzukiDF6D4LogTwoInterval.Contains (Real.log 2) := by
  have hL := Real.sum_range_le_log_div
    (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 18
  have hU := Real.log_div_le_sum_range_add
    (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 18
  unfold suzukiDF6D4LogTwoInterval RationalInterval.Contains
  norm_num [Finset.sum_range_succ] at hL hU ⊢
  constructor
  · linarith
  · linarith

theorem suzukiDF6D4PiInterval_contains :
    suzukiDF6D4PiInterval.Contains Real.pi := by
  unfold suzukiDF6D4PiInterval RationalInterval.Contains
  norm_num
  constructor
  · have h := Real.pi_gt_d20.le
    norm_num at h
    exact h
  · have h := Real.pi_lt_d20.le
    norm_num at h
    exact h

theorem suzukiDF6D4SqrtTwoInterval_contains :
    suzukiDF6D4SqrtTwoInterval.Contains (Real.sqrt 2) := by
  unfold suzukiDF6D4SqrtTwoInterval RationalInterval.Contains
  norm_num
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · have hlowerSq :
        (141421356237309 / 100000000000000 : Real) ^ 2 < 2 := by
      norm_num
    nlinarith

  · have hupperSq :
        2 < (141421356237310 / 100000000000000 : Real) ^ 2 := by
      norm_num
    nlinarith

private theorem exp_neg_4286781467006_lower :
    (65136954088297 / 100000000000000 : Real) ≤
      Real.exp (-4286781467006 / 10000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-4286781467006 / 10000000000000 : Real))
    (n := 18) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem exp_neg_4286781467005_upper :
    Real.exp (-4286781467005 / 10000000000000 : Real) ≤
      (65136954088305 / 100000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-4286781467005 / 10000000000000 : Real))
    (n := 18) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem exp_neg_98025814346856_lower :
    (37521422724647 / 100000000000000 : Real) ≤
      Real.exp (-98025814346856 / 100000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-98025814346856 / 100000000000000 : Real))
    (n := 20) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem exp_neg_98025814346853_upper :
    Real.exp (-98025814346853 / 100000000000000 : Real) ≤
      (37521422724649 / 100000000000000 : Real) := by
  have h := Real.exp_bound
    (x := (-98025814346853 / 100000000000000 : Real))
    (n := 20) (by norm_num) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem suzukiDF6D4AStarInterval_contains :
    suzukiDF6D4AStarInterval.Contains suzukiProjectAStar := by
  have hL := suzukiDF6D4LogTwoInterval_contains
  have hS := suzukiDF6D4SqrtTwoInterval_contains
  unfold suzukiDF6D4LogTwoInterval RationalInterval.Contains at hL
  unfold suzukiDF6D4SqrtTwoInterval RationalInterval.Contains at hS
  norm_num at hL hS
  have hLLower :
      (69314718055994 / 100000000000000 : Real) ≤ Real.log 2 := by
    norm_num
    exact hL.1
  have hLUpper :
      Real.log 2 ≤ (69314718055995 / 100000000000000 : Real) := by
    norm_num
    exact hL.2
  have hSLower :
      (141421356237309 / 100000000000000 : Real) ≤ Real.sqrt 2 := by
    norm_num
    exact hS.1
  have hSUpper :
      Real.sqrt 2 ≤ (141421356237310 / 100000000000000 : Real) := by
    norm_num
    exact hS.2
  let y : Real := -(Real.sqrt 2 * Real.log 2)
  have hprodLowerBase :
      (141421356237309 / 100000000000000 : Real) *
          (69314718055994 / 100000000000000 : Real) ≤
        Real.sqrt 2 * Real.log 2 :=
    mul_le_mul hSLower hLLower (by norm_num) (Real.sqrt_nonneg 2)
  have hprodLower :
      (98025814346853 / 100000000000000 : Real) ≤
        Real.sqrt 2 * Real.log 2 := by
    calc
      (98025814346853 / 100000000000000 : Real) ≤
          (141421356237309 / 100000000000000 : Real) *
            (69314718055994 / 100000000000000 : Real) := by norm_num
      _ ≤ Real.sqrt 2 * Real.log 2 := hprodLowerBase
  have hprodUpperBase :
      Real.sqrt 2 * Real.log 2 ≤
        (141421356237310 / 100000000000000 : Real) *
          (69314718055995 / 100000000000000 : Real) :=
    mul_le_mul hSUpper hLUpper (Real.log_pos (by norm_num)).le (by norm_num)
  have hprodUpper :
      Real.sqrt 2 * Real.log 2 ≤
        (98025814346856 / 100000000000000 : Real) := by
    calc
      Real.sqrt 2 * Real.log 2 ≤
          (141421356237310 / 100000000000000 : Real) *
            (69314718055995 / 100000000000000 : Real) := hprodUpperBase
      _ ≤ (98025814346856 / 100000000000000 : Real) := by norm_num
  have hyLower :
      (-98025814346856 / 100000000000000 : Real) ≤ y := by
    dsimp only [y]
    linarith
  have hyUpper :
      y ≤ (-98025814346853 / 100000000000000 : Real) := by
    dsimp only [y]
    linarith
  have hExpLower :
      (37521422724647 / 100000000000000 : Real) ≤ Real.exp y :=
    exp_neg_98025814346856_lower.trans (Real.exp_le_exp.mpr hyLower)
  have hExpUpper :
      Real.exp y ≤ (37521422724649 / 100000000000000 : Real) :=
    (Real.exp_le_exp.mpr hyUpper).trans exp_neg_98025814346853_upper
  have hExpSquare :
      Real.exp (-2 * Real.sqrt 2 * Real.log 2) =
        Real.exp y * Real.exp y := by
    rw [show -2 * Real.sqrt 2 * Real.log 2 = y + y by
      dsimp only [y]
      ring, Real.exp_add]
  have hDoubleExpLower :
      (37521422724647 / 100000000000000 : Real) ^ 2 ≤
        Real.exp (-2 * Real.sqrt 2 * Real.log 2) := by
    rw [hExpSquare]
    nlinarith [Real.exp_pos y]
  have hDoubleExpUpper :
      Real.exp (-2 * Real.sqrt 2 * Real.log 2) ≤
        (37521422724649 / 100000000000000 : Real) ^ 2 := by
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
      4 * (4286781467005 / 10000000000000 : Real) ^ 2 -
          2 * (4286781467005 / 10000000000000 : Real) *
            (69314718055994 / 100000000000000 : Real) ≤
        (37521422724647 / 100000000000000 : Real) ^ 2 := by
    norm_num
  have hlowerAlgebra :
      4 * (4286781467005 / 10000000000000 : Real) ^ 2 -
          2 * (4286781467005 / 10000000000000 : Real) * Real.log 2 ≤
        Real.exp (-2 * Real.sqrt 2 * Real.log 2) := by
    nlinarith
  have hlowerSquare :
      (4 * (4286781467005 / 10000000000000 : Real) - Real.log 2) ^ 2 ≤ z := by
    dsimp only [z]
    nlinarith
  have hlowerRoot :
      4 * (4286781467005 / 10000000000000 : Real) - Real.log 2 ≤
        Real.sqrt z := by
    have hleftNonneg :
        0 ≤ 4 * (4286781467005 / 10000000000000 : Real) - Real.log 2 := by
      nlinarith
    nlinarith
  have hupperNumerical :
      (37521422724649 / 100000000000000 : Real) ^ 2 ≤
        4 * (4286781467006 / 10000000000000 : Real) ^ 2 -
          2 * (4286781467006 / 10000000000000 : Real) *
            (69314718055995 / 100000000000000 : Real) := by
    norm_num
  have hupperAlgebra :
      Real.exp (-2 * Real.sqrt 2 * Real.log 2) ≤
        4 * (4286781467006 / 10000000000000 : Real) ^ 2 -
          2 * (4286781467006 / 10000000000000 : Real) * Real.log 2 := by
    nlinarith
  have hupperSquare :
      z ≤
        (4 * (4286781467006 / 10000000000000 : Real) - Real.log 2) ^ 2 := by
    dsimp only [z]
    nlinarith
  have hupperRoot :
      Real.sqrt z ≤
        4 * (4286781467006 / 10000000000000 : Real) - Real.log 2 := by
    have hrightNonneg :
        0 ≤ 4 * (4286781467006 / 10000000000000 : Real) - Real.log 2 := by
      nlinarith
    nlinarith
  unfold suzukiDF6D4AStarInterval RationalInterval.Contains
  unfold suzukiProjectAStar
  change
    ((4286781467005 / 10000000000000 : Rat) : Real) ≤
        (Real.log 2 + Real.sqrt z) / 4 ∧
      (Real.log 2 + Real.sqrt z) / 4 ≤
        ((4286781467006 / 10000000000000 : Rat) : Real)
  norm_num
  constructor <;> linarith

theorem suzukiDF6D4ExpNegAStarInterval_contains :
    suzukiDF6D4ExpNegAStarInterval.Contains
      (Real.exp (-suzukiProjectAStar)) := by
  have hA := suzukiDF6D4AStarInterval_contains
  unfold suzukiDF6D4AStarInterval RationalInterval.Contains at hA
  norm_num at hA
  have hNegLower :
      (-4286781467006 / 10000000000000 : Real) ≤
        -suzukiProjectAStar := by
    linarith
  have hNegUpper :
      -suzukiProjectAStar ≤
        (-4286781467005 / 10000000000000 : Real) := by
    linarith
  unfold suzukiDF6D4ExpNegAStarInterval RationalInterval.Contains
  norm_num
  constructor
  · have h := exp_neg_4286781467006_lower.trans
        (Real.exp_le_exp.mpr hNegLower)
    norm_num at h ⊢
    exact h
  · have h := (Real.exp_le_exp.mpr hNegUpper).trans
        exp_neg_4286781467005_upper
    norm_num at h ⊢
    exact h

/-! ## Euler-Mascheroni enclosure -/

private theorem suzukiDF6D4_log_one_add_inv_upper
    (n : Nat) (hn : 0 < n) :
    Real.log (1 + 1 / (n : Real)) ≤
      1 / ((n : Real) + 1) +
        1 / (2 * (n : Real) * ((n : Real) + 1)) := by
  let x : Real := 1 / (2 * (n : Real) + 1)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by positivity)]
    norm_num
    exact_mod_cast hn
  have h := Real.log_div_le_sum_range_add hx0 hx1 1
  norm_num at h
  have hratio : (1 + x) / (1 - x) = 1 + 1 / (n : Real) := by
    dsimp [x]
    field_simp
    ring
  calc
    Real.log (1 + 1 / (n : Real)) =
        Real.log ((1 + x) / (1 - x)) := congrArg Real.log hratio.symm
    _ ≤ 2 * (x + x ^ 3 / (1 - x ^ 2)) := by linarith
    _ = 1 / ((n : Real) + 1) +
        1 / (2 * (n : Real) * ((n : Real) + 1)) := by
      dsimp [x]
      rw [show 1 - (1 / (2 * (n : Real) + 1)) ^ 2 =
          4 * (n : Real) * ((n : Real) + 1) /
            (2 * (n : Real) + 1) ^ 2 by
        field_simp
        ring]
      field_simp
      ring

private theorem suzukiDF6D4_log_one_add_inv_lower
    (n : Nat) (hn : 0 < n) :
    1 / ((n : Real) + 1) +
        2 / ((2 * (n : Real) + 1) * (2 * (n : Real) + 3)) ≤
      Real.log (1 + 1 / (n : Real)) := by
  let x : Real := 1 / (2 * (n : Real) + 1)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by positivity)]
    norm_num
    exact_mod_cast hn
  have h := Real.sum_range_le_log_div hx0 hx1 1
  norm_num at h
  have hratio : (1 + x) / (1 - x) = 1 + 1 / (n : Real) := by
    dsimp [x]
    field_simp
    ring
  calc
    1 / ((n : Real) + 1) +
          2 / ((2 * (n : Real) + 1) * (2 * (n : Real) + 3)) ≤
        2 * x := by
      dsimp [x]
      field_simp
      nlinarith [show (0 : Real) < n by exact_mod_cast hn]
    _ ≤ Real.log ((1 + x) / (1 - x)) := by linarith
    _ = Real.log (1 + 1 / (n : Real)) := congrArg Real.log hratio

private noncomputable def suzukiDF6D4EulerLower (n : Nat) : Real :=
  (harmonic (n + 1) : Real) - Real.log ((n + 1 : Nat) : Real) -
    1 / (2 * (((n + 1 : Nat) : Real)))

private noncomputable def suzukiDF6D4EulerUpper (n : Nat) : Real :=
  (harmonic (n + 1) : Real) - Real.log ((n + 1 : Nat) : Real) -
    1 / (2 * (((n + 1 : Nat) : Real)) + 1)

private theorem monotone_suzukiDF6D4EulerLower :
    Monotone suzukiDF6D4EulerLower := by
  apply monotone_nat_of_le_succ
  intro n
  have hlog := suzukiDF6D4_log_one_add_inv_upper (n + 1) (by omega)
  push_cast at hlog
  unfold suzukiDF6D4EulerLower
  nth_rewrite 2 [harmonic_succ]
  push_cast
  rw [show Real.log ((n : Real) + 1 + 1) =
      Real.log ((n : Real) + 1) +
        Real.log (1 + 1 / ((n : Real) + 1)) by
    rw [← Real.log_mul
      (by positivity : (n : Real) + 1 ≠ 0)
      (by positivity : 1 + 1 / ((n : Real) + 1) ≠ 0)]
    congr 1
    field_simp]
  have hcorr :
      1 / (2 * ((n : Real) + 1)) -
          1 / (2 * ((n : Real) + 1 + 1)) =
        1 / (2 * ((n : Real) + 1) * ((n : Real) + 1 + 1)) := by
    field_simp
    ring
  rw [← hcorr] at hlog
  simp only [one_div] at hlog ⊢
  linarith

private theorem antitone_suzukiDF6D4EulerUpper :
    Antitone suzukiDF6D4EulerUpper := by
  apply antitone_nat_of_succ_le
  intro n
  have hlog := suzukiDF6D4_log_one_add_inv_lower (n + 1) (by omega)
  push_cast at hlog
  unfold suzukiDF6D4EulerUpper
  nth_rewrite 1 [harmonic_succ]
  push_cast
  rw [show Real.log ((n : Real) + 1 + 1) =
      Real.log ((n : Real) + 1) +
        Real.log (1 + 1 / ((n : Real) + 1)) by
    rw [← Real.log_mul
      (by positivity : (n : Real) + 1 ≠ 0)
      (by positivity : 1 + 1 / ((n : Real) + 1) ≠ 0)]
    congr 1
    field_simp]
  have hcorr :
      1 / (2 * ((n : Real) + 1) + 1) -
          1 / (2 * ((n : Real) + 1 + 1) + 1) =
        2 / ((2 * ((n : Real) + 1) + 1) *
          (2 * ((n : Real) + 1) + 3)) := by
    field_simp
    ring
  rw [← hcorr] at hlog
  simp only [one_div] at hlog ⊢
  linarith

private theorem tendsto_suzukiDF6D4EulerLower :
    Tendsto suzukiDF6D4EulerLower atTop
      (nhds Real.eulerMascheroniConstant) := by
  have hcorr : Tendsto
      (fun n : Nat => 1 / (2 * (((n + 1 : Nat) : Real))))
      atTop (nhds 0) := by
    have h :=
      (tendsto_const_nhds : Tendsto
        (fun _ : Nat => (1 / 2 : Real)) atTop (nhds (1 / 2))).mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    convert h using 1 <;> norm_num
    funext n
    field_simp
  change Tendsto (fun n : Nat =>
    (harmonic (n + 1) : Real) - Real.log ((n + 1 : Nat) : Real) -
      1 / (2 * (((n + 1 : Nat) : Real)))) atTop
        (nhds Real.eulerMascheroniConstant)
  simpa only [Function.comp_apply, sub_zero] using
    (Real.tendsto_harmonic_sub_log.comp
      (tendsto_add_atTop_nat 1)).sub hcorr

private theorem tendsto_suzukiDF6D4EulerUpper :
    Tendsto suzukiDF6D4EulerUpper atTop
      (nhds Real.eulerMascheroniConstant) := by
  have hcorr : Tendsto
      (fun n : Nat => 1 / (2 * ((n : Real) + 1) + 1))
      atTop (nhds 0) := by
    apply squeeze_zero (fun n : Nat => by positivity)
      (fun n : Nat => show
        1 / (2 * (n + 1 : Real) + 1) ≤ 1 / ((n : Real) + 1) by
          apply one_div_le_one_div_of_le (by positivity)
          linarith)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun n : Nat =>
    (harmonic (n + 1) : Real) - Real.log ((n + 1 : Nat) : Real) -
      1 / (2 * (((n + 1 : Nat) : Real)) + 1)) atTop
        (nhds Real.eulerMascheroniConstant)
  simpa only [Function.comp_apply, sub_zero, Nat.cast_add, Nat.cast_one] using
    (Real.tendsto_harmonic_sub_log.comp
      (tendsto_add_atTop_nat 1)).sub hcorr

theorem suzukiDF6D4_euler_corrected_bounds
    (N : Nat) (hN : 0 < N) :
    (harmonic N : Real) - Real.log N - 1 / (2 * (N : Real)) ≤
      Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant ≤
      (harmonic N : Real) - Real.log N -
        1 / (2 * (N : Real) + 1) := by
  let n := N - 1
  have hn : n + 1 = N := by omega
  constructor
  · have h := monotone_suzukiDF6D4EulerLower.ge_of_tendsto
      tendsto_suzukiDF6D4EulerLower n
    unfold suzukiDF6D4EulerLower at h
    rw [hn] at h
    exact h
  · have h := antitone_suzukiDF6D4EulerUpper.le_of_tendsto
      tendsto_suzukiDF6D4EulerUpper n
    unfold suzukiDF6D4EulerUpper at h
    rw [hn] at h
    exact h

private theorem suzukiDF6D4EulerPartialRat_bounds :
    (57721566 / 100000000 : Rat) +
          14 * (6931471808 / 10000000000 : Rat) +
          1 / (2 * 16384 : Rat) ≤
        harmonic 16384 ∧
      harmonic 16384 ≤
        (57721567 / 100000000 : Rat) +
          14 * (6931471803 / 10000000000 : Rat) +
          1 / (2 * 16384 + 1 : Rat) := by
  native_decide

theorem suzukiDF6D4EulerInterval_contains :
    suzukiDF6D4EulerInterval.Contains Real.eulerMascheroniConstant := by
  have hcorrected := suzukiDF6D4_euler_corrected_bounds 16384 (by norm_num)
  have hlogTwo := suzukiDF6D4LogTwoInterval_contains
  have hrat := suzukiDF6D4EulerPartialRat_bounds
  have hlogPower : Real.log (16384 : Real) = 14 * Real.log 2 := by
    rw [show (16384 : Real) = 2 ^ 14 by norm_num, Real.log_pow]
    norm_num
  have hcast16384 : ((16384 : Nat) : Real) = (16384 : Real) := by
    norm_num
  rw [hcast16384, hlogPower] at hcorrected
  unfold suzukiDF6D4LogTwoInterval RationalInterval.Contains at hlogTwo
  unfold suzukiDF6D4EulerInterval RationalInterval.Contains
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

/-! ## Catalan and zeta-three enclosures -/

/-- Catalan's constant in the normalization used by the endpoint Gamma
series.  The alternating definition makes the truncation error elementary
and keeps the analytic constant independent of generated certificate data. -/
noncomputable def suzukiDF6D4CatalanConstant : Real :=
  ∑' n : Nat, (-1 : Real) ^ n / ((2 * n + 1 : Nat) : Real) ^ 2

/-- The real zeta-three constant used by the endpoint Gamma series. -/
noncomputable def suzukiDF6D4ZetaThree : Real :=
  ∑' n : Nat, 1 / ((n + 1 : Nat) : Real) ^ 3

def suzukiDF6D4CatalanInterval : RationalInterval :=
  ⟨91596559 / 100000000, 91596560 / 100000000⟩

def suzukiDF6D4ZetaThreeInterval : RationalInterval :=
  ⟨120205690 / 100000000, 120205691 / 100000000⟩

private theorem summable_suzukiDF6D4CatalanMagnitude :
    Summable (fun n : Nat =>
      1 / ((2 * n + 1 : Nat) : Real) ^ 2) := by
  have h : Summable (fun n : Nat => (((n : Real) ^ 2)⁻¹)) :=
    (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
  have hshift : Summable
      (fun n : Nat => 1 / ((n + 1 : Nat) : Real) ^ 2) := by
    simpa only [one_div] using (summable_nat_add_iff 1).2 h
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hshift
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast (show n + 1 ≤ 2 * n + 1 by omega)

private theorem antitone_suzukiDF6D4CatalanMagnitude :
    Antitone (fun n : Nat =>
      1 / ((2 * n + 1 : Nat) : Real) ^ 2) := by
  intro m n hmn
  have hcast : ((2 * m + 1 : Nat) : Real) ≤ (2 * n + 1 : Nat) := by
    exact_mod_cast (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hmn) 1)
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) hcast 2

private theorem suzukiDF6D4Catalan_error_bound (N : Nat) :
    |suzukiDF6D4CatalanConstant -
        ∑ n ∈ Finset.range N,
          (-1 : Real) ^ n / ((2 * n + 1 : Nat) : Real) ^ 2| ≤
      1 / ((2 * N + 1 : Nat) : Real) ^ 2 := by
  unfold suzukiDF6D4CatalanConstant
  simpa only [div_eq_mul_inv, one_mul] using
    alternating_series_error_bound
      (fun n : Nat => 1 / ((2 * n + 1 : Nat) : Real) ^ 2)
      antitone_suzukiDF6D4CatalanMagnitude
      summable_suzukiDF6D4CatalanMagnitude N

private def suzukiDF6D4CatalanPartialRat (N : Nat) : Rat :=
  ∑ n ∈ Finset.range N,
    (-1 : Rat) ^ n / ((2 * n + 1 : Nat) : Rat) ^ 2

private theorem suzukiDF6D4CatalanPartialRat_cast (N : Nat) :
    (suzukiDF6D4CatalanPartialRat N : Real) =
      ∑ n ∈ Finset.range N,
        (-1 : Real) ^ n / ((2 * n + 1 : Nat) : Real) ^ 2 := by
  unfold suzukiDF6D4CatalanPartialRat
  push_cast
  rfl

private theorem suzukiDF6D4CatalanPartialRat_bounds :
    (91596559 / 100000000 : Rat) +
          1 / ((2 * 16384 + 1 : Nat) : Rat) ^ 2 ≤
        suzukiDF6D4CatalanPartialRat 16384 ∧
      suzukiDF6D4CatalanPartialRat 16384 +
          1 / ((2 * 16384 + 1 : Nat) : Rat) ^ 2 ≤
        (91596560 / 100000000 : Rat) := by
  native_decide

theorem suzukiDF6D4CatalanInterval_contains :
    suzukiDF6D4CatalanInterval.Contains suzukiDF6D4CatalanConstant := by
  have herr := suzukiDF6D4Catalan_error_bound 16384
  have hpartial := suzukiDF6D4CatalanPartialRat_bounds
  have hcast := suzukiDF6D4CatalanPartialRat_cast 16384
  rw [abs_le] at herr
  rw [← hcast] at herr
  unfold suzukiDF6D4CatalanInterval RationalInterval.Contains
  constructor
  · have hpartialLower := (Rat.cast_le (K := Real)).2 hpartial.1
    rw [Rat.cast_add] at hpartialLower
    norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_ofNat] at hpartialLower ⊢
    linarith
  · have hpartialUpper := (Rat.cast_le (K := Real)).2 hpartial.2
    rw [Rat.cast_add] at hpartialUpper
    norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_ofNat] at hpartialUpper ⊢
    linarith

private theorem summable_suzukiDF6D4ZetaThreeSeries :
    Summable (fun n : Nat =>
      1 / ((n + 1 : Nat) : Real) ^ 3) := by
  have h : Summable (fun n : Nat => (((n : Real) ^ 3)⁻¹)) :=
    (Real.summable_nat_pow_inv (p := 3)).2 (by norm_num)
  simpa only [one_div] using (summable_nat_add_iff 1).2 h

private theorem suzukiDF6D4ZetaThree_tail_le (N : Nat) (hN : 0 < N) :
    (∑' n : Nat, 1 / ((n + N + 1 : Nat) : Real) ^ 3) ≤
      1 / (N : Real) ^ 2 := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro k
    calc
      ∑ n ∈ Finset.range k,
            1 / ((n + N + 1 : Nat) : Real) ^ 3 ≤
          ∑ n ∈ Finset.range k,
            (1 / ((n + N : Nat) : Real) ^ 2 -
              1 / ((n + N + 1 : Nat) : Real) ^ 2) := by
        apply Finset.sum_le_sum
        intro n hn
        have hx : (0 : Real) < (n + N : Nat) := by
          exact_mod_cast Nat.add_pos_right n hN
        have hx1 : (0 : Real) < (n + N + 1 : Nat) := by positivity
        push_cast
        field_simp
        ring_nf
        nlinarith [sq_nonneg ((n : Real) + N)]
      _ = 1 / (N : Real) ^ 2 -
          1 / ((k + N : Nat) : Real) ^ 2 := by
        induction k with
        | zero => simp
        | succ k ih =>
            rw [Finset.sum_range_succ, ih]
            push_cast
            ring
      _ ≤ 1 / (N : Real) ^ 2 :=
        sub_le_self _ (by positivity)

private def suzukiDF6D4ZetaThreePartialRat (N : Nat) : Rat :=
  ∑ n ∈ Finset.range N, 1 / ((n + 1 : Nat) : Rat) ^ 3

private theorem suzukiDF6D4ZetaThreePartialRat_cast (N : Nat) :
    (suzukiDF6D4ZetaThreePartialRat N : Real) =
      ∑ n ∈ Finset.range N,
        1 / ((n + 1 : Nat) : Real) ^ 3 := by
  unfold suzukiDF6D4ZetaThreePartialRat
  push_cast
  rfl

private theorem suzukiDF6D4ZetaThreePartialRat_bounds :
    (120205690 / 100000000 : Rat) ≤
        suzukiDF6D4ZetaThreePartialRat 16384 ∧
      suzukiDF6D4ZetaThreePartialRat 16384 +
          1 / (16384 : Rat) ^ 2 ≤
        (120205691 / 100000000 : Rat) := by
  native_decide

theorem suzukiDF6D4ZetaThreeInterval_contains :
    suzukiDF6D4ZetaThreeInterval.Contains suzukiDF6D4ZetaThree := by
  have hsum := summable_suzukiDF6D4ZetaThreeSeries
  have hsplit := hsum.sum_add_tsum_nat_add 16384
  have htail := suzukiDF6D4ZetaThree_tail_le 16384 (by norm_num)
  have htailNonneg :
      0 ≤ ∑' n : Nat,
        1 / ((n + 16384 + 1 : Nat) : Real) ^ 3 :=
    tsum_nonneg (fun n => by positivity)
  have hpartial := suzukiDF6D4ZetaThreePartialRat_bounds
  have hcast := suzukiDF6D4ZetaThreePartialRat_cast 16384
  rw [← hcast] at hsplit
  unfold suzukiDF6D4ZetaThreeInterval RationalInterval.Contains
  constructor
  · have hpartialLower := (Rat.cast_le (K := Real)).2 hpartial.1
    calc
      ((120205690 / 100000000 : Rat) : Real) ≤
          (suzukiDF6D4ZetaThreePartialRat 16384 : Real) := hpartialLower
      _ ≤ (suzukiDF6D4ZetaThreePartialRat 16384 : Real) +
          ∑' n : Nat, 1 / ((n + 16384 + 1 : Nat) : Real) ^ 3 :=
        le_add_of_nonneg_right htailNonneg
      _ = suzukiDF6D4ZetaThree := hsplit
  · have hpartialUpper := (Rat.cast_le (K := Real)).2 hpartial.2
    rw [Rat.cast_add] at hpartialUpper
    norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_ofNat] at hpartialUpper ⊢
    have htail' :
        (∑' n : Nat,
            1 / ((n + 16384 + 1 : Nat) : Real) ^ 3) ≤
          1 / 268435456 := by
      norm_num at htail ⊢
      exact htail
    calc
      suzukiDF6D4ZetaThree =
          (suzukiDF6D4ZetaThreePartialRat 16384 : Real) +
            ∑' n : Nat,
              1 / ((n + 16384 + 1 : Nat) : Real) ^ 3 := hsplit.symm
      _ ≤ (suzukiDF6D4ZetaThreePartialRat 16384 : Real) +
          1 / 268435456 :=
        by
          simpa [add_comm] using
            add_le_add_left htail'
              (suzukiDF6D4ZetaThreePartialRat 16384 : Real)
      _ ≤ 120205691 / 100000000 := hpartialUpper

end M100
end Experiments
end RiemannHypothesisProject
