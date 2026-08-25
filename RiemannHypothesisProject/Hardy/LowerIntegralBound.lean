import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import RiemannHypothesisProject.Hardy.HardyFunctionNormalization
import RiemannHypothesisProject.Hardy.ZetaFirstApproximation

/-!
# Hardy's explicit lower integral bound

This file supplies the H4B elementary estimate and endpoint assembly.  It
consumes the exact H1 finite zeta approximation and the H4A norm identity,
with fixed constants and no asymptotic notation.
-/

open Complex MeasureTheory Set

namespace RiemannHypothesisProject

namespace Hardy

noncomputable section

/-- A positive integer critical-line mode is a fixed coefficient times a pure
exponential in the height variable. -/
theorem cpow_neg_criticalLinePoint_eq_mode
    {n : Nat} (hn : 0 < n) (t : Real) :
    (n : Complex) ^ (-criticalLinePoint t) =
      (n : Complex) ^ (-criticalLinePoint 0) *
        Complex.exp ((-Complex.I * Complex.log (n : Complex)) * t) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'),
    ← Complex.exp_add]
  congr 1
  simp only [criticalLinePoint]
  push_cast
  ring

/-- Every nonconstant critical-line Dirichlet mode has an explicitly bounded
integral on a dyadic interval.  The coarse constant `4` follows from
`log n ≥ 1/2` for `n ≥ 2`. -/
theorem norm_integral_cpow_neg_criticalLinePoint_le
    {n : Nat} (hn : 2 ≤ n) (T : Real) :
    ‖∫ t in T..2 * T, (n : Complex) ^ (-criticalLinePoint t)‖ ≤
      4 / Real.sqrt n := by
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn_real_pos : 0 < (n : Real) := by exact_mod_cast hn_pos
  have hlog_half : (1 / 2 : Real) ≤ Real.log n := by
    have hbase := Real.one_sub_inv_le_log_of_pos hn_real_pos
    have hinv : (n : Real)⁻¹ ≤ 1 / 2 := by
      have hn_real : (2 : Real) ≤ n := by exact_mod_cast hn
      simpa [one_div] using
        (inv_le_inv₀ hn_real_pos (by norm_num : (0 : Real) < 2)).2 hn_real
    linarith
  have hlog_pos : 0 < Real.log n := (by norm_num : (0 : Real) < 1 / 2).trans_le hlog_half
  have hlog : Complex.log (n : Complex) = (Real.log n : Complex) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn_real_pos.le]
  let c : Complex := -Complex.I * (Real.log n : Complex)
  have hc : c ≠ 0 := by
    dsimp only [c]
    apply mul_ne_zero
    · exact neg_ne_zero.mpr Complex.I_ne_zero
    · exact Complex.ofReal_ne_zero.mpr hlog_pos.ne'
  have hmode :
      (fun t : Real => (n : Complex) ^ (-criticalLinePoint t)) =
        fun t : Real => (n : Complex) ^ (-criticalLinePoint 0) *
          Complex.exp (c * t) := by
    funext t
    rw [cpow_neg_criticalLinePoint_eq_mode hn_pos t, hlog]
  rw [hmode]
  rw [intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (a := T) (b := 2 * T) hc]
  have hnumerator :
      ‖Complex.exp (c * ((2 * T : Real) : Complex)) -
          Complex.exp (c * (T : Complex))‖ ≤ 2 := by
    have hnorm_exp (x : Real) :
        ‖Complex.exp (c * (x : Complex))‖ = 1 := by
      rw [Complex.norm_exp]
      have hc_re : c.re = 0 := by
        dsimp only [c]
        simp only [Complex.mul_re, Complex.neg_re, Complex.I_re,
          Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, mul_zero,
          sub_zero]
      have hre : (c * (x : Complex)).re = 0 := by
        rw [Complex.mul_re, hc_re]
        norm_num
      rw [hre, Real.exp_zero]
    calc
      _ ≤ ‖Complex.exp (c * ((2 * T : Real) : Complex))‖ +
          ‖Complex.exp (c * (T : Complex))‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm_exp, hnorm_exp]; norm_num
  have hcoeff :
      ‖(n : Complex) ^ (-criticalLinePoint 0)‖ = 1 / Real.sqrt n := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hn_real_pos]
    have hre : (-criticalLinePoint 0).re = -(1 / 2 : Real) := by
      norm_num [criticalLinePoint]
    rw [hre]
    rw [show (-(1 / 2 : Real)) = -(1 / 2 : Real) by rfl,
      Real.rpow_neg hn_real_pos.le, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  have hc_norm : ‖c‖ = Real.log n := by
    dsimp only [c]
    rw [norm_mul, norm_neg, norm_I, one_mul,
      Complex.norm_real,
      Real.norm_of_nonneg hlog_pos.le]
  rw [norm_mul, norm_div, hcoeff, hc_norm]
  calc
    (1 / Real.sqrt n) *
        (‖Complex.exp (c * ((2 * T : Real) : Complex)) -
            Complex.exp (c * (T : Complex))‖ / Real.log n) ≤
      (1 / Real.sqrt n) * (2 / Real.log n) := by
        gcongr
    _ ≤ (1 / Real.sqrt n) * 4 := by
      gcongr
      rw [div_le_iff₀ hlog_pos]
      nlinarith
    _ = 4 / Real.sqrt n := by ring

/-- The elementary finite coefficient estimate used in H4B. -/
theorem sum_Icc_one_div_sqrt_le_two_mul_sqrt (m : Nat) :
    ∑ k ∈ Finset.Icc 1 m, (1 / Real.sqrt k : Real) ≤ 2 * Real.sqrt m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
      have hm_nonneg : (0 : Real) ≤ m := by positivity
      have hsucc_pos : (0 : Real) < (m + 1 : Nat) := by positivity
      have hsqrt_succ_pos :
          0 < Real.sqrt ((m + 1 : Nat) : Real) := Real.sqrt_pos.2 hsucc_pos
      have hstep :
          2 * Real.sqrt m + 1 / Real.sqrt ((m + 1 : Nat) : Real) ≤
            2 * Real.sqrt ((m + 1 : Nat) : Real) := by
        have hm_sq : (Real.sqrt m) ^ 2 = (m : Real) := Real.sq_sqrt hm_nonneg
        have hsucc_sq :
            (Real.sqrt ((m + 1 : Nat) : Real)) ^ 2 = ((m + 1 : Nat) : Real) :=
          Real.sq_sqrt (by positivity)
        have hincrement :
            1 / Real.sqrt ((m + 1 : Nat) : Real) ≤
              2 * (Real.sqrt ((m + 1 : Nat) : Real) - Real.sqrt m) := by
          rw [div_le_iff₀ hsqrt_succ_pos]
          norm_num [Nat.cast_add, Nat.cast_one] at hsucc_sq ⊢
          nlinarith [sq_nonneg (Real.sqrt m - Real.sqrt ((m : Real) + 1))]
        linarith
      calc
        _ ≤ 2 * Real.sqrt m + 1 / Real.sqrt ((m + 1 : Nat) : Real) :=
          add_le_add ih le_rfl
        _ ≤ 2 * Real.sqrt ((m + 1 : Nat) : Real) := hstep

/-- The complete nonconstant part of the finite Dirichlet sum contributes at
most `8 * sqrt m` after integration over any dyadic interval. -/
theorem norm_sum_Icc_integral_cpow_neg_criticalLinePoint_le
    (m : Nat) (T : Real) :
    ‖∑ k ∈ Finset.Icc 2 m,
        ∫ t in T..2 * T, (k : Complex) ^ (-criticalLinePoint t)‖ ≤
      8 * Real.sqrt m := by
  have hsubset : Finset.Icc 2 m ⊆ Finset.Icc 1 m := by
    intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  have hsubsum :
      ∑ k ∈ Finset.Icc 2 m, (1 / Real.sqrt k : Real) ≤
        ∑ k ∈ Finset.Icc 1 m, (1 / Real.sqrt k : Real) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => by positivity
  calc
    _ ≤ ∑ k ∈ Finset.Icc 2 m,
        ‖∫ t in T..2 * T, (k : Complex) ^ (-criticalLinePoint t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 2 m, 4 / Real.sqrt k := by
      exact Finset.sum_le_sum fun k hk =>
        norm_integral_cpow_neg_criticalLinePoint_le (Finset.mem_Icc.mp hk).1 T
    _ = 4 * ∑ k ∈ Finset.Icc 2 m, (1 / Real.sqrt k : Real) := by
      simp only [div_eq_mul_inv, Finset.mul_sum, one_mul]
    _ ≤ 4 * ∑ k ∈ Finset.Icc 1 m, (1 / Real.sqrt k : Real) := by
      gcongr
    _ ≤ 4 * (2 * Real.sqrt m) := by
      gcongr
      exact sum_Icc_one_div_sqrt_le_two_mul_sqrt m
    _ = 8 * Real.sqrt m := by ring

/-- Each positive integer critical-line mode is continuous in height. -/
theorem continuous_cpow_neg_criticalLinePoint {n : Nat} (hn : 0 < n) :
    Continuous (fun t : Real => (n : Complex) ^ (-criticalLinePoint t)) := by
  have hmode :
      (fun t : Real => (n : Complex) ^ (-criticalLinePoint t)) =
        fun t : Real => (n : Complex) ^ (-criticalLinePoint 0) *
          Complex.exp ((-Complex.I * Complex.log (n : Complex)) * t) := by
    funext t
    exact cpow_neg_criticalLinePoint_eq_mode hn t
  rw [hmode]
  fun_prop

/-- Termwise integration of the H1 cutoff sum, with the `n = 1` main term
isolated exactly. -/
theorem integral_sum_Icc_cpow_neg_criticalLinePoint_eq_main_add
    {m : Nat} (hm : 1 ≤ m) (T : Real) :
    (∫ t in T..2 * T,
        ∑ k ∈ Finset.Icc 1 m,
          (k : Complex) ^ (-criticalLinePoint t)) =
      T + ∑ k ∈ Finset.Icc 2 m,
        ∫ t in T..2 * T, (k : Complex) ^ (-criticalLinePoint t) := by
  have hsplit : Finset.Icc 1 m = insert 1 (Finset.Icc 2 m) := by
    exact (Finset.insert_Icc_succ_left_eq_Icc hm).symm
  have hone : 1 ∉ Finset.Icc 2 m := by simp
  have htermwise :
      (∫ t in T..2 * T,
          ∑ k ∈ Finset.Icc 2 m,
            (k : Complex) ^ (-criticalLinePoint t)) =
        ∑ k ∈ Finset.Icc 2 m,
          ∫ t in T..2 * T, (k : Complex) ^ (-criticalLinePoint t) := by
    apply intervalIntegral.integral_finsetSum
    intro k hk
    exact (continuous_cpow_neg_criticalLinePoint
      (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hk).1)).intervalIntegrable _ _
  have hsum_integrable :
      IntervalIntegrable
        (fun t : Real => ∑ k ∈ Finset.Icc 2 m,
          (k : Complex) ^ (-criticalLinePoint t)) volume T (2 * T) := by
    exact (continuous_finsetSum _ fun k hk =>
      continuous_cpow_neg_criticalLinePoint
        (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hk).1)).intervalIntegrable _ _
  rw [hsplit]
  simp only [Finset.sum_insert, hone, not_false_eq_true, Nat.cast_one,
    Complex.one_cpow]
  rw [intervalIntegral.integral_add intervalIntegrable_const hsum_integrable]
  rw [htermwise]
  simp only [intervalIntegral.integral_const]
  have hlength : 2 * T - T = T := by ring
  rw [hlength]
  have hsmul : T • (1 : Complex) = (T : Complex) := by simp
  rw [hsmul]

/-- The H1 cutoff lies below the dyadic height itself. -/
theorem zetaFirstApproximationCutoff_le_height
    {T : Real} (hT : 0 ≤ T) :
    (zetaFirstApproximationCutoff T : Real) ≤ T := by
  have hfloor :
      (zetaFirstApproximationCutoff T : Real) ≤ 3 * T / Real.pi := by
    simpa [zetaFirstApproximationCutoff] using
      Nat.floor_le (by positivity : 0 ≤ 3 * T / Real.pi)
  have hratio : 3 * T / Real.pi ≤ T := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  exact hfloor.trans hratio

/-- Zeta is continuous along the whole critical line. -/
theorem continuous_riemannZeta_criticalLine :
    Continuous (fun t : Real => riemannZeta (criticalLinePoint t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hne : criticalLinePoint t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [criticalLinePoint] at hre
  exact (differentiableAt_riemannZeta hne).continuousAt.comp
    continuous_criticalLinePoint.continuousAt

/-- Integrating a uniform H1 remainder over `[T,2T]` costs exactly one factor
of the interval length. -/
theorem norm_integral_zetaFirstApproximationRemainder_le
    {K T : Real} (hT : 0 < T)
    (happrox : ∀ t : Real, T ≤ t → t ≤ 2 * T →
      ‖riemannZeta (criticalLinePoint t) -
        ∑ k ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
          (k : Complex) ^ (-criticalLinePoint t)‖ ≤ K / Real.sqrt T) :
    ‖∫ t in T..2 * T,
        (riemannZeta (criticalLinePoint t) -
          ∑ k ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
            (k : Complex) ^ (-criticalLinePoint t))‖ ≤
      K * Real.sqrt T := by
  have hT_le : T ≤ 2 * T := by linarith
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := T) (b := 2 * T) (C := K / Real.sqrt T)
    (f := fun t : Real =>
      riemannZeta (criticalLinePoint t) -
        ∑ k ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
          (k : Complex) ^ (-criticalLinePoint t))
    (fun t ht => by
      rw [uIoc_of_le hT_le] at ht
      exact happrox t (le_of_lt ht.1) ht.2)
  have hsqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  calc
    _ ≤ (K / Real.sqrt T) * |2 * T - T| := hbound
    _ = (K / Real.sqrt T) * T := by
      rw [abs_of_pos (by linarith)]
      ring
    _ = K * Real.sqrt T := by
      field_simp [hsqrt_pos.ne']
      rw [Real.sq_sqrt hT.le]

/-- Above the H1 threshold the exact cutoff contains the main mode `n = 1`. -/
theorem one_le_zetaFirstApproximationCutoff
    {T : Real} (hT : 2 ≤ T) :
    1 ≤ zetaFirstApproximationCutoff T := by
  apply Nat.le_floor
  rw [le_div_iff₀ Real.pi_pos]
  norm_num
  nlinarith [Real.pi_lt_four]

/-- Quantitative lower bound for the complex zeta integral before applying
the H4A norm identity. -/
theorem norm_integral_riemannZeta_criticalLine_ge
    {K T : Real} (hT : 2 ≤ T)
    (happrox : ∀ t : Real, T ≤ t → t ≤ 2 * T →
      ‖riemannZeta (criticalLinePoint t) -
        ∑ k ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
          (k : Complex) ^ (-criticalLinePoint t)‖ ≤ K / Real.sqrt T) :
    T - (K + 8) * Real.sqrt T ≤
      ‖∫ t in T..2 * T, riemannZeta (criticalLinePoint t)‖ := by
  let m := zetaFirstApproximationCutoff T
  let D : Real → Complex := fun t =>
    ∑ k ∈ Finset.Icc 1 m, (k : Complex) ^ (-criticalLinePoint t)
  let Q : Complex := ∑ k ∈ Finset.Icc 2 m,
    ∫ t in T..2 * T, (k : Complex) ^ (-criticalLinePoint t)
  let R : Complex := ∫ t in T..2 * T,
    (riemannZeta (criticalLinePoint t) - D t)
  let Z : Complex := ∫ t in T..2 * T, riemannZeta (criticalLinePoint t)
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hm : 1 ≤ m := one_le_zetaFirstApproximationCutoff hT
  have hD_cont : Continuous D := by
    dsimp only [D]
    exact continuous_finsetSum _ fun k hk =>
      continuous_cpow_neg_criticalLinePoint
        (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hk).1)
  have hZ_int : IntervalIntegrable
      (fun t : Real => riemannZeta (criticalLinePoint t)) volume T (2 * T) :=
    continuous_riemannZeta_criticalLine.intervalIntegrable _ _
  have hD_int : IntervalIntegrable D volume T (2 * T) :=
    hD_cont.intervalIntegrable _ _
  have hsub := intervalIntegral.integral_sub hZ_int hD_int
  have hD_eval : (∫ t in T..2 * T, D t) = (T : Complex) + Q := by
    simpa only [D, Q, m] using
      integral_sum_Icc_cpow_neg_criticalLinePoint_eq_main_add hm T
  have hdecomp : Z = (T : Complex) + Q + R := by
    dsimp only [Z, R]
    rw [show (∫ t in T..2 * T,
        riemannZeta (criticalLinePoint t) - D t) =
      (∫ t in T..2 * T, riemannZeta (criticalLinePoint t)) -
        ∫ t in T..2 * T, D t from hsub]
    rw [hD_eval]
    ring
  have hQ : ‖Q‖ ≤ 8 * Real.sqrt T := by
    have hraw := norm_sum_Icc_integral_cpow_neg_criticalLinePoint_le m T
    have hm_le : (m : Real) ≤ T := by
      exact zetaFirstApproximationCutoff_le_height hT_pos.le
    have hsqrt_le : Real.sqrt m ≤ Real.sqrt T := Real.sqrt_le_sqrt hm_le
    exact hraw.trans (by gcongr)
  have hR : ‖R‖ ≤ K * Real.sqrt T := by
    dsimp only [R, D, m]
    exact norm_integral_zetaFirstApproximationRemainder_le hT_pos happrox
  have hmain : T ≤ ‖Z‖ + ‖Q‖ + ‖R‖ := by
    calc
      T = ‖(T : Complex)‖ := by simp [abs_of_pos hT_pos]
      _ = ‖Z - Q - R‖ := by
        rw [hdecomp]
        congr 1
        ring
      _ ≤ ‖Z - Q‖ + ‖R‖ := norm_sub_le _ _
      _ ≤ (‖Z‖ + ‖Q‖) + ‖R‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
  dsimp only [Z] at hmain ⊢
  linarith

/-- H4B: beyond a fixed threshold, the absolute Hardy-function integral on
`[T, 2T]` is at least `T / 2`. -/
theorem exists_hardyLowerIntegralBound :
    ∃ T₁ : Real, 2 ≤ T₁ ∧ ∀ T : Real, T₁ ≤ T →
      T / 2 ≤ ∫ t in T..2 * T, |hardyFunctionReal t| := by
  obtain ⟨K, hK, T₀, hT₀, happrox⟩ := exists_uniform_zetaFirstApproximation
  let B : Real := K + 8
  let T₁ : Real := max T₀ (4 * B ^ 2)
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  refine ⟨T₁, hT₀.trans (le_max_left _ _), ?_⟩
  intro T hT
  have hT₀T : T₀ ≤ T := (le_max_left _ _).trans hT
  have hTlarge : 4 * B ^ 2 ≤ T := (le_max_right _ _).trans hT
  have hTtwo : 2 ≤ T := hT₀.trans hT₀T
  have hT_nonneg : 0 ≤ T := le_trans (by norm_num) hTtwo
  have happrox' : ∀ t : Real, T ≤ t → t ≤ 2 * T →
      ‖riemannZeta (criticalLinePoint t) -
        ∑ k ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
          (k : Complex) ^ (-criticalLinePoint t)‖ ≤ K / Real.sqrt T := by
    intro t ht ht'
    have happ := happrox T t hT₀T ht ht'
    norm_num [criticalLinePoint] at happ ⊢
    exact happ
  have hzeta := norm_integral_riemannZeta_criticalLine_ge hTtwo happrox'
  have hnorm_integral :
      ‖∫ t in T..2 * T, riemannZeta (criticalLinePoint t)‖ ≤
        ∫ t in T..2 * T, ‖riemannZeta (criticalLinePoint t)‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hintegral_eq :
      (∫ t in T..2 * T, ‖riemannZeta (criticalLinePoint t)‖) =
        ∫ t in T..2 * T, |hardyFunctionReal t| := by
    apply intervalIntegral.integral_congr
    intro t _
    exact (abs_hardyFunctionReal t).symm
  rw [hintegral_eq] at hnorm_integral
  have hsqrt_sq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hsqrt_large : 2 * B ≤ Real.sqrt T := by
    nlinarith
  have herror : B * Real.sqrt T ≤ T / 2 := by
    have hproduct : 0 ≤ Real.sqrt T * (Real.sqrt T - 2 * B) :=
      mul_nonneg hsqrt_nonneg (sub_nonneg.mpr hsqrt_large)
    nlinarith
  dsimp only [B] at herror
  linarith

end

end Hardy

end RiemannHypothesisProject
