import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RiemannHypothesisProject.RiemannVonMangoldtPublishedBounds

/-!
# Elementary bounds for published `N(T)` source terms

This file proves coarse analytic tail bounds for the named Riemann-von
Mangoldt main term and the Bellotti-Wong/Hasanalizade-Shen-Wong error terms.

The bounds are deliberately generous. Their role is to discharge the
polynomial-tail fields in concrete published-source inputs, not to optimize
constants.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/--
The Riemann-von Mangoldt main term is bounded by a coarse quadratic envelope on
the cutoff-2 tail.
-/
theorem riemannVonMangoldtMainTerm_cutoffTwo_le_quadratic
    (n : Nat) :
    riemannVonMangoldtMainTerm ((n + 2 : Nat) : Real) <=
      100 * |(n : Real) + 1| ^ (2 : Real) := by
  let T : Real := ((n + 2 : Nat) : Real)
  let R : Real := |(n : Real) + 1| ^ (2 : Real)
  have hT_nonneg : 0 <= T := by positivity
  have hden₁_pos : 0 < 2 * Real.pi := by positivity
  have hden₂_pos : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  have hden₁_one : 1 <= 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hden₂_one : 1 <= 2 * Real.pi * Real.exp 1 := by
    have hexp_one : 1 <= Real.exp 1 := Real.one_le_exp zero_le_one
    nlinarith
  have hcoef_nonneg : 0 <= T / (2 * Real.pi) := by positivity
  have harg_nonneg : 0 <= T / (2 * Real.pi * Real.exp 1) := by positivity
  have hcoef_le_T : T / (2 * Real.pi) <= T := by
    rw [div_le_iff₀ hden₁_pos]
    nlinarith [mul_le_mul_of_nonneg_left hden₁_one hT_nonneg]
  have harg_le_T : T / (2 * Real.pi * Real.exp 1) <= T := by
    rw [div_le_iff₀ hden₂_pos]
    nlinarith [mul_le_mul_of_nonneg_left hden₂_one hT_nonneg]
  have hlog_le :
      Real.log (T / (2 * Real.pi * Real.exp 1)) <=
        T / (2 * Real.pi * Real.exp 1) :=
    Real.log_le_self harg_nonneg
  have hmain_le_square :
      T / (2 * Real.pi) *
          Real.log (T / (2 * Real.pi * Real.exp 1)) <=
        T * T := by
    exact (mul_le_mul_of_nonneg_left hlog_le hcoef_nonneg).trans
      (mul_le_mul hcoef_le_T harg_le_T harg_nonneg hT_nonneg)
  have hT_le : T <= 2 * ((n : Real) + 1) := by
    dsimp [T]
    norm_num [Nat.cast_add]
    nlinarith [(Nat.cast_nonneg n : (0 : Real) <= n)]
  have hy_nonneg : 0 <= (n : Real) + 1 := by positivity
  have hT_square_le : T * T <= 4 * R := by
    have htwoy_nonneg : 0 <= 2 * ((n : Real) + 1) := by
      nlinarith [(Nat.cast_nonneg n : (0 : Real) <= n)]
    have hsq := mul_le_mul hT_le hT_le hT_nonneg htwoy_nonneg
    have hR : R = ((n : Real) + 1) ^ 2 := by
      dsimp [R]
      rw [abs_of_nonneg hy_nonneg]
      exact Real.rpow_natCast ((n : Real) + 1) 2
    rw [hR]
    nlinarith
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    positivity
  have h4_le_100 : 4 * R <= 100 * R := by nlinarith
  dsimp [riemannVonMangoldtMainTerm]
  change T / (2 * Real.pi) *
      Real.log (T / (2 * Real.pi * Real.exp 1)) <=
    100 * R
  exact hmain_le_square.trans (hT_square_le.trans h4_le_100)

/--
A generic coarse cutoff-2 quadratic bound for terms of the form
`a * log T + b * log (log T) + c`, with small nonnegative coefficients.
-/
theorem linearLogLogErrorTerm_cutoffTwo_le_quadratic
    {a b c : Real}
    (ha_nonneg : 0 <= a) (ha_le_one : a <= 1)
    (hb_nonneg : 0 <= b) (hb_le_one : b <= 1)
    (hc_le_ten : c <= 10)
    (n : Nat) :
    a * Real.log ((n + 2 : Nat) : Real) +
        b * Real.log (Real.log ((n + 2 : Nat) : Real)) + c <=
      100 * |(n : Real) + 1| ^ (2 : Real) := by
  let T : Real := ((n + 2 : Nat) : Real)
  let Y : Real := (n : Real) + 1
  let R : Real := |(n : Real) + 1| ^ (2 : Real)
  have hT_nonneg : 0 <= T := by positivity
  have hT_gt_one : 1 < T := by
    dsimp [T]
    norm_num [Nat.cast_add]
    nlinarith [(Nat.cast_nonneg n : (0 : Real) <= n)]
  have hlogT_nonneg : 0 <= Real.log T :=
    le_of_lt (Real.log_pos hT_gt_one)
  have hlogT_le_T : Real.log T <= T :=
    Real.log_le_self hT_nonneg
  have hloglogT_le_T : Real.log (Real.log T) <= T :=
    (Real.log_le_self hlogT_nonneg).trans hlogT_le_T
  have ha_log_le_T : a * Real.log T <= T := by
    have hmul := mul_le_mul_of_nonneg_left hlogT_le_T ha_nonneg
    have hscale : a * T <= T := by nlinarith
    exact hmul.trans hscale
  have hb_loglog_le_T : b * Real.log (Real.log T) <= T := by
    have hmul := mul_le_mul_of_nonneg_left hloglogT_le_T hb_nonneg
    have hscale : b * T <= T := by nlinarith
    exact hmul.trans hscale
  have hT_le : T <= 2 * Y := by
    dsimp [T, Y]
    norm_num [Nat.cast_add]
    nlinarith [(Nat.cast_nonneg n : (0 : Real) <= n)]
  have hY_ge_one : 1 <= Y := by
    dsimp [Y]
    nlinarith [(Nat.cast_nonneg n : (0 : Real) <= n)]
  have hY_nonneg : 0 <= Y := by linarith
  have hY_le_sq : Y <= Y ^ 2 := by
    have hprod : 0 <= Y * (Y - 1) :=
      mul_nonneg hY_nonneg (sub_nonneg.mpr hY_ge_one)
    nlinarith
  have hR : R = Y ^ 2 := by
    dsimp [R, Y]
    rw [abs_of_nonneg (by positivity : 0 <= (n : Real) + 1)]
    exact Real.rpow_natCast ((n : Real) + 1) 2
  have hsum_linear :
      a * Real.log T + b * Real.log (Real.log T) + c <=
        2 * T + 10 := by
    nlinarith
  have hlinear_quad : 2 * T + 10 <= 100 * R := by
    rw [hR]
    nlinarith
  change a * Real.log T + b * Real.log (Real.log T) + c <=
    100 * R
  exact hsum_linear.trans hlinear_quad

/-- The Bellotti-Wong error term has a coarse quadratic cutoff-2 tail. -/
theorem bellottiWongErrorTerm_cutoffTwo_le_quadratic
    (n : Nat) :
    bellottiWongErrorTerm ((n + 2 : Nat) : Real) <=
      100 * |(n : Real) + 1| ^ (2 : Real) := by
  dsimp [bellottiWongErrorTerm]
  exact linearLogLogErrorTerm_cutoffTwo_le_quadratic
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) n

/--
The Hasanalizade-Shen-Wong error term has a coarse quadratic cutoff-2 tail.
-/
theorem hasanalizadeShenWongErrorTerm_cutoffTwo_le_quadratic
    (n : Nat) :
    hasanalizadeShenWongErrorTerm ((n + 2 : Nat) : Real) <=
      100 * |(n : Real) + 1| ^ (2 : Real) := by
  dsimp [hasanalizadeShenWongErrorTerm]
  exact linearLogLogErrorTerm_cutoffTwo_le_quadratic
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) n

/--
A nonnegative linear index bound is dominated by a coarse quadratic cutoff-2
tail. This is useful for the axis/trivial-zero contribution, where the natural
remaining target is an `O(n)` bound on the real-axis window.
-/
theorem linearIndexBound_cutoffTwo_le_quadratic
    {axisSlope : Real} (axisSlope_nonneg : 0 <= axisSlope) (n : Nat) :
    axisSlope * (((n + 2 : Nat) : Real) + 1) <=
      (3 * axisSlope) * |(n : Real) + 1| ^ (2 : Real) := by
  let Y : Real := (n : Real) + 1
  have hY_ge_one : 1 <= Y := by
    dsimp [Y]
    nlinarith [(Nat.cast_nonneg n : (0 : Real) <= (n : Real))]
  have hY_nonneg : 0 <= Y := by linarith
  have hY_le_sq : Y <= Y ^ 2 := by
    have hprod : 0 <= Y * (Y - 1) :=
      mul_nonneg hY_nonneg (sub_nonneg.mpr hY_ge_one)
    nlinarith
  have hindex_eq : (((n + 2 : Nat) : Real) + 1) = Y + 2 := by
    dsimp [Y]
    norm_num [Nat.cast_add]
    ring
  have hindex_le : (((n + 2 : Nat) : Real) + 1) <= 3 * Y := by
    rw [hindex_eq]
    nlinarith [hY_ge_one]
  have hindex_le_sq : (((n + 2 : Nat) : Real) + 1) <= 3 * Y ^ 2 := by
    nlinarith
  have hR : |(n : Real) + 1| ^ (2 : Real) = Y ^ 2 := by
    dsimp [Y]
    rw [abs_of_nonneg (by positivity : 0 <= (n : Real) + 1)]
    exact Real.rpow_natCast ((n : Real) + 1) 2
  rw [hR]
  nlinarith [mul_le_mul_of_nonneg_left hindex_le_sq axisSlope_nonneg]

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
