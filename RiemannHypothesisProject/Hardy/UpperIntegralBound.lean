import RiemannHypothesisProject.Hardy.LowerIntegralBound
import RiemannHypothesisProject.Hardy.OscillatoryIntegralEstimates

/-!
# Hardy's explicit upper oscillatory integral bound

This file supplies the H4C endpoint assembly. It consumes the exact H1--H3
analytic estimates and the H4A Hardy normalization, with fixed constants and
no asymptotic notation.
-/

open Complex MeasureTheory Set

namespace RiemannHypothesisProject

namespace Hardy

noncomputable section

/-- The H2 phase combined with the `n`th H1 monomial is exactly the H3 Hardy
phase, up to the fixed `-pi/8` factor. -/
theorem criticalLineStirlingPhase_sub_log_mode
    {n : Nat} (hn : 0 < n) {t : Real} (ht : 0 < t) :
    criticalLineStirlingPhase t - t * Real.log n =
      hardyOscillatoryPhase n t - Real.pi / 8 := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have hden : 0 < 2 * Real.pi * (n : Real) ^ 2 := by positivity
  have hlogPow : Real.log ((n : Real) ^ 2) = 2 * Real.log n := by
    rw [Real.log_pow]
    norm_num
  have hlogDen :
      Real.log (2 * Real.pi * (n : Real) ^ 2) =
        Real.log (2 * Real.pi) + 2 * Real.log n := by
    rw [Real.log_mul htwoPi.ne' (pow_ne_zero 2 hnReal.ne'), hlogPow]
  have hlog :
      Real.log (t / (2 * Real.pi * (n : Real) ^ 2)) =
        Real.log (t / (2 * Real.pi)) - 2 * Real.log n := by
    rw [Real.log_div ht.ne' hden.ne', Real.log_div ht.ne' htwoPi.ne', hlogDen]
    ring
  rw [criticalLineStirlingPhase, hardyOscillatoryPhase, hlog]
  ring

/-- The critical-line monomial at height zero is its positive real
`1 / sqrt n` coefficient. -/
theorem cpow_neg_criticalLinePoint_zero
    {n : Nat} (hn : 0 < n) :
    (n : Complex) ^ (-criticalLinePoint 0) =
      ((1 / Real.sqrt n : Real) : Complex) := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hpoint : -criticalLinePoint 0 = ((-(1 / 2 : Real) : Real) : Complex) := by
    norm_num [criticalLinePoint]
  rw [hpoint]
  change ((n : Real) : Complex) ^ ((-(1 / 2 : Real) : Real) : Complex) = _
  rw [← Complex.ofReal_cpow hnReal.le]
  congr 1
  rw [Real.rpow_neg hnReal.le, ← Real.sqrt_eq_rpow]
  ring

/-- Exact mode identity used to transport the H1 finite sum to the H3
oscillatory estimates. -/
theorem exp_stirlingPhase_mul_cpow_eq_hardyOscillatoryMode
    {n : Nat} (hn : 0 < n) {t : Real} (ht : 0 < t) :
    Complex.exp (Complex.I * criticalLineStirlingPhase t) *
        (n : Complex) ^ (-criticalLinePoint t) =
      ((1 / Real.sqrt n : Real) : Complex) *
        Complex.exp (-Complex.I * (Real.pi / 8)) *
          firstDerivativeOscillation (hardyOscillatoryPhase n) t := by
  rw [cpow_neg_criticalLinePoint_eq_mode hn t,
    cpow_neg_criticalLinePoint_zero hn]
  have hphase := criticalLineStirlingPhase_sub_log_mode hn ht
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hlog : Complex.log (n : Complex) = (Real.log (n : Real) : Complex) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnReal.le]
  have hexponent :
      Complex.I * criticalLineStirlingPhase t +
          (-Complex.I * Complex.log (n : Complex)) * t =
        -Complex.I * (Real.pi / 8) +
          Complex.I * hardyOscillatoryPhase n t := by
    calc
      _ = Complex.I *
          ((criticalLineStirlingPhase t - t * Real.log n : Real) : Complex) := by
            rw [hlog]
            push_cast
            ring
      _ = Complex.I *
          ((hardyOscillatoryPhase n t - Real.pi / 8 : Real) : Complex) := by
            rw [hphase]
      _ = _ := by
        push_cast
        ring
  calc
    _ = ((1 / Real.sqrt n : Real) : Complex) *
        (Complex.exp (Complex.I * criticalLineStirlingPhase t) *
          Complex.exp ((-Complex.I * Complex.log (n : Complex)) * t)) := by
          ring
    _ = ((1 / Real.sqrt n : Real) : Complex) *
        Complex.exp
          (Complex.I * criticalLineStirlingPhase t +
            (-Complex.I * Complex.log (n : Complex)) * t) := by
          rw [Complex.exp_add]
    _ = ((1 / Real.sqrt n : Real) : Complex) *
        Complex.exp
          (-Complex.I * (Real.pi / 8) +
            Complex.I * hardyOscillatoryPhase n t) := by rw [hexponent]
    _ = _ := by
      rw [Complex.exp_add]
      simp only [firstDerivativeOscillation, mul_assoc]

/-- The exact integer split corresponding to `3 * sqrt (T / pi)`. -/
def hardyOscillatorySplitCutoff (T : Real) : Nat :=
  ⌊3 * Real.sqrt (T / Real.pi)⌋₊

/-- One integrated oscillatory mode, with its H1 coefficient and fixed H2
phase factor retained explicitly. -/
def hardyOscillatoryModeIntegral (n : Nat) (T : Real) : Complex :=
  ((1 / Real.sqrt n : Real) : Complex) *
    Complex.exp (-Complex.I * (Real.pi / 8)) *
      ∫ t in T..2 * T,
        firstDerivativeOscillation (hardyOscillatoryPhase n) t

/-- Every mode satisfies the stationary-safe H3 estimate. -/
theorem norm_hardyOscillatoryModeIntegral_le_twenty
    {n : Nat} (hn : 0 < n) {T : Real} (hT : 0 < T) :
    ‖hardyOscillatoryModeIntegral n T‖ ≤
      (1 / Real.sqrt n) * (20 * Real.sqrt T) := by
  have hcoeff : 0 ≤ (1 / Real.sqrt n : Real) := by positivity
  have hphaseNorm :
      ‖Complex.exp (-Complex.I * (Real.pi / 8))‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num
  rw [hardyOscillatoryModeIntegral, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hcoeff, hphaseNorm, mul_one]
  gcongr
  exact norm_integral_hardyOscillatoryPhase_le_twenty_mul_sqrt hn hT

/-- Modes above the exact source split satisfy the H3 first-derivative
estimate. -/
theorem norm_hardyOscillatoryModeIntegral_le_nine
    {n : Nat} (hn : 0 < n) {T : Real} (hT : 0 < T)
    (hnlarge : hardyOscillatorySplitCutoff T < n) :
    ‖hardyOscillatoryModeIntegral n T‖ ≤
      (1 / Real.sqrt n) * 9 := by
  have hcoeff : 0 ≤ (1 / Real.sqrt n : Real) := by positivity
  have hphaseNorm :
      ‖Complex.exp (-Complex.I * (Real.pi / 8))‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num
  have hthreshold : 3 * Real.sqrt (T / Real.pi) < (n : Real) := by
    have hfloor : 3 * Real.sqrt (T / Real.pi) <
        ((hardyOscillatorySplitCutoff T + 1 : Nat) : Real) := by
      simpa [hardyOscillatorySplitCutoff, Nat.cast_add, Nat.cast_one] using
        (Nat.lt_floor_add_one
          (3 * Real.sqrt (T / Real.pi) : Real))
    have hsucc : hardyOscillatorySplitCutoff T + 1 ≤ n := by omega
    exact hfloor.trans_le (by exact_mod_cast hsucc)
  rw [hardyOscillatoryModeIntegral, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hcoeff, hphaseNorm, mul_one]
  gcongr
  exact norm_integral_hardyOscillatoryPhase_le_nine_of_large_mode
    hn hT hthreshold

/-- The modes at or below the source split contribute at most
`40 * sqrt T * sqrt N`, where `N` is the exact floored split. -/
theorem norm_sum_small_hardyOscillatoryModeIntegral_le
    (m : Nat) {T : Real} (hT : 0 < T) :
    ‖∑ n ∈ (Finset.Icc 1 m).filter
          (fun n => n ≤ hardyOscillatorySplitCutoff T),
        hardyOscillatoryModeIntegral n T‖ ≤
      40 * Real.sqrt T * Real.sqrt (hardyOscillatorySplitCutoff T) := by
  let N := hardyOscillatorySplitCutoff T
  let s := (Finset.Icc 1 m).filter (fun n => n ≤ N)
  have hsubset : s ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn.1).1, hn.2⟩
  have hsum :
      ∑ n ∈ s, (1 / Real.sqrt n : Real) ≤ 2 * Real.sqrt N := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => by positivity)).trans
        (sum_Icc_one_div_sqrt_le_two_mul_sqrt N)
  change ‖∑ n ∈ s, hardyOscillatoryModeIntegral n T‖ ≤ _
  calc
    _ ≤ ∑ n ∈ s, ‖hardyOscillatoryModeIntegral n T‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s,
        (1 / Real.sqrt n) * (20 * Real.sqrt T) := by
      exact Finset.sum_le_sum fun n hn =>
        norm_hardyOscillatoryModeIntegral_le_twenty
          (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp
            (Finset.mem_filter.mp hn).1).1) hT
    _ = (20 * Real.sqrt T) *
        ∑ n ∈ s, (1 / Real.sqrt n : Real) := by
      simp only [mul_comm (1 / Real.sqrt _), Finset.mul_sum]
    _ ≤ (20 * Real.sqrt T) * (2 * Real.sqrt N) := by
      gcongr
    _ = 40 * Real.sqrt T * Real.sqrt N := by ring

/-- The modes strictly above the source split contribute at most
`18 * sqrt m`. -/
theorem norm_sum_large_hardyOscillatoryModeIntegral_le
    (m : Nat) {T : Real} (hT : 0 < T) :
    ‖∑ n ∈ (Finset.Icc 1 m).filter
          (fun n => ¬n ≤ hardyOscillatorySplitCutoff T),
        hardyOscillatoryModeIntegral n T‖ ≤
      18 * Real.sqrt m := by
  let N := hardyOscillatorySplitCutoff T
  let s := (Finset.Icc 1 m).filter (fun n => ¬n ≤ N)
  have hsubset : s ⊆ Finset.Icc 1 m := Finset.filter_subset _ _
  have hsum :
      ∑ n ∈ s, (1 / Real.sqrt n : Real) ≤ 2 * Real.sqrt m := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => by positivity)).trans
        (sum_Icc_one_div_sqrt_le_two_mul_sqrt m)
  change ‖∑ n ∈ s, hardyOscillatoryModeIntegral n T‖ ≤ _
  calc
    _ ≤ ∑ n ∈ s, ‖hardyOscillatoryModeIntegral n T‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, (1 / Real.sqrt n) * 9 := by
      exact Finset.sum_le_sum fun n hn =>
        norm_hardyOscillatoryModeIntegral_le_nine
          (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp
            (Finset.mem_filter.mp hn).1).1) hT
          (lt_of_not_ge (Finset.mem_filter.mp hn).2)
    _ = 9 * ∑ n ∈ s, (1 / Real.sqrt n : Real) := by
      simp only [mul_comm (1 / Real.sqrt _), Finset.mul_sum]
    _ ≤ 9 * (2 * Real.sqrt m) := by gcongr
    _ = 18 * Real.sqrt m := by ring

/-- Explicit two-range estimate for the integrated H1 oscillatory main sum. -/
theorem norm_sum_hardyOscillatoryModeIntegral_le
    (m : Nat) {T : Real} (hT : 0 < T) :
    ‖∑ n ∈ Finset.Icc 1 m, hardyOscillatoryModeIntegral n T‖ ≤
      40 * Real.sqrt T * Real.sqrt (hardyOscillatorySplitCutoff T) +
        18 * Real.sqrt m := by
  let p : Nat → Prop := fun n => n ≤ hardyOscillatorySplitCutoff T
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 m) p (hardyOscillatoryModeIntegral · T)
  rw [← hsplit]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_sum_small_hardyOscillatoryModeIntegral_le m hT)
    (norm_sum_large_hardyOscillatoryModeIntegral_le m hT))

/-- The exact source split is no larger than `3 * sqrt T`. -/
theorem hardyOscillatorySplitCutoff_le_three_mul_sqrt
    {T : Real} (hT : 0 ≤ T) :
    (hardyOscillatorySplitCutoff T : Real) ≤ 3 * Real.sqrt T := by
  have harg : 0 ≤ 3 * Real.sqrt (T / Real.pi) := by positivity
  have hfloor : (hardyOscillatorySplitCutoff T : Real) ≤
      3 * Real.sqrt (T / Real.pi) := by
    simpa [hardyOscillatorySplitCutoff] using Nat.floor_le harg
  have hquot : T / Real.pi ≤ T := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  exact hfloor.trans (by gcongr)

/-- The square root of the split cutoff has the required fourth-root size. -/
theorem sqrt_hardyOscillatorySplitCutoff_le
    {T : Real} (hT : 0 ≤ T) :
    Real.sqrt (hardyOscillatorySplitCutoff T) ≤
      2 * Real.sqrt (Real.sqrt T) := by
  have hcut := hardyOscillatorySplitCutoff_le_three_mul_sqrt hT
  have hcutFour : (hardyOscillatorySplitCutoff T : Real) ≤
      4 * Real.sqrt T := by
    have hsqrt : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
    linarith
  have hsqrt := Real.sqrt_le_sqrt hcutFour
  have hsqrtFour : Real.sqrt (4 : Real) = 2 := by
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  calc
    Real.sqrt (hardyOscillatorySplitCutoff T) ≤
        Real.sqrt (4 * Real.sqrt T) := hsqrt
    _ = Real.sqrt 4 * Real.sqrt (Real.sqrt T) := by
      rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
    _ = 2 * Real.sqrt (Real.sqrt T) := by rw [hsqrtFour]

/-- Elementary identity exposing the `T^(3/4)` scale used by H4C. -/
theorem sqrt_mul_sqrt_sqrt_eq_rpow_three_quarters
    {T : Real} (hT : 0 < T) :
    Real.sqrt T * Real.sqrt (Real.sqrt T) = T ^ (3 / 4 : Real) := by
  calc
    Real.sqrt T * Real.sqrt (Real.sqrt T) =
        T ^ (1 / 2 : Real) * (T ^ (1 / 2 : Real)) ^ (1 / 2 : Real) := by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    _ = T ^ (1 / 2 : Real) * T ^ ((1 / 2 : Real) * (1 / 2 : Real)) := by
      rw [Real.rpow_mul hT.le]
    _ = T ^ ((1 / 2 : Real) + (1 / 2 : Real) * (1 / 2 : Real)) := by
      rw [Real.rpow_add hT]
    _ = T ^ (3 / 4 : Real) := by norm_num

/-- The integrated phased H1 main sum is bounded by the fixed constant `98`
at the exact `T^(3/4)` scale. -/
theorem norm_sum_cutoff_hardyOscillatoryModeIntegral_le
    {T : Real} (hT : 1 ≤ T) :
    ‖∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
        hardyOscillatoryModeIntegral n T‖ ≤
      98 * T ^ (3 / 4 : Real) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hraw := norm_sum_hardyOscillatoryModeIntegral_le
    (zetaFirstApproximationCutoff T) hTpos
  have hsplit := sqrt_hardyOscillatorySplitCutoff_le hTpos.le
  have hm := zetaFirstApproximationCutoff_le_height hTpos.le
  have hsqrtm : Real.sqrt (zetaFirstApproximationCutoff T) ≤ Real.sqrt T :=
    Real.sqrt_le_sqrt hm
  have hscale := sqrt_mul_sqrt_sqrt_eq_rpow_three_quarters hTpos
  have hsqrtOne : 1 ≤ Real.sqrt T := by
    simpa using Real.sqrt_le_sqrt hT
  have hsqrtSqrtOne : 1 ≤ Real.sqrt (Real.sqrt T) := by
    simpa using Real.sqrt_le_sqrt hsqrtOne
  have hsqrt_le_scale : Real.sqrt T ≤ T ^ (3 / 4 : Real) := by
    calc
      Real.sqrt T = Real.sqrt T * 1 := by ring
      _ ≤ Real.sqrt T * Real.sqrt (Real.sqrt T) := by gcongr
      _ = T ^ (3 / 4 : Real) := hscale
  calc
    _ ≤ 40 * Real.sqrt T *
          Real.sqrt (hardyOscillatorySplitCutoff T) +
        18 * Real.sqrt (zetaFirstApproximationCutoff T) := hraw
    _ ≤ 40 * Real.sqrt T * (2 * Real.sqrt (Real.sqrt T)) +
        18 * Real.sqrt T := by gcongr
    _ = 80 * T ^ (3 / 4 : Real) + 18 * Real.sqrt T := by
      rw [← hscale]
      ring
    _ ≤ 80 * T ^ (3 / 4 : Real) + 18 * T ^ (3 / 4 : Real) := by
      gcongr
    _ = 98 * T ^ (3 / 4 : Real) := by ring

/-- The norm of a positive critical-line Dirichlet mode is exactly its
`1 / sqrt n` coefficient. -/
theorem norm_cpow_neg_criticalLinePoint
    {n : Nat} (hn : 0 < n) (t : Real) :
    ‖(n : Complex) ^ (-criticalLinePoint t)‖ = 1 / Real.sqrt n := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  rw [Complex.norm_natCast_cpow_of_pos hn]
  have hre : (-criticalLinePoint t).re = -(1 / 2 : Real) := by
    norm_num [criticalLinePoint]
  rw [hre, Real.rpow_neg hnReal.le, ← Real.sqrt_eq_rpow]
  ring

/-- The H1 cutoff sum has the elementary pointwise bound `2 * sqrt m`. -/
theorem norm_sum_Icc_cpow_neg_criticalLinePoint_le
    (m : Nat) (t : Real) :
    ‖∑ n ∈ Finset.Icc 1 m,
        (n : Complex) ^ (-criticalLinePoint t)‖ ≤ 2 * Real.sqrt m := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 m,
        ‖(n : Complex) ^ (-criticalLinePoint t)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 m, (1 / Real.sqrt n : Real) := by
      apply Finset.sum_congr rfl
      intro n hnmem
      exact norm_cpow_neg_criticalLinePoint
        (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hnmem).1) t
    _ ≤ 2 * Real.sqrt m := sum_Icc_one_div_sqrt_le_two_mul_sqrt m

/-- Termwise integration transports one phased H1 monomial exactly to its
H3 oscillatory mode integral. -/
theorem integral_exp_stirlingPhase_mul_cpow_eq_hardyOscillatoryMode
    {n : Nat} (hn : 0 < n) {T : Real} (hT : 0 < T) :
    (∫ t in T..2 * T,
        Complex.exp (Complex.I * criticalLineStirlingPhase t) *
          (n : Complex) ^ (-criticalLinePoint t)) =
      hardyOscillatoryModeIntegral n T := by
  rw [hardyOscillatoryModeIntegral,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have hTle : T ≤ 2 * T := by linarith
  rw [Set.uIcc_of_le hTle] at ht
  exact exp_stirlingPhase_mul_cpow_eq_hardyOscillatoryMode hn
    (hT.trans_le ht.1)

/-- The phased H1 cutoff integral is exactly the finite sum controlled by
the H3 low/high frequency split. -/
theorem integral_exp_stirlingPhase_mul_cutoffSum_eq
    {m : Nat} {T : Real} (hT : 0 < T) :
    (∫ t in T..2 * T,
        Complex.exp (Complex.I * criticalLineStirlingPhase t) *
          ∑ n ∈ Finset.Icc 1 m,
            (n : Complex) ^ (-criticalLinePoint t)) =
      ∑ n ∈ Finset.Icc 1 m, hardyOscillatoryModeIntegral n T := by
  have hTle : T ≤ 2 * T := by linarith
  have hint (n : Nat) (hnmem : n ∈ Finset.Icc 1 m) :
      IntervalIntegrable
        (fun t : Real =>
          ((1 / Real.sqrt n : Real) : Complex) *
            Complex.exp (-Complex.I * (Real.pi / 8)) *
              firstDerivativeOscillation (hardyOscillatoryPhase n) t)
        volume T (2 * T) := by
    have hn : 0 < n :=
      lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hnmem).1
    have hcont : ContinuousOn
        (fun t : Real =>
          ((1 / Real.sqrt n : Real) : Complex) *
            Complex.exp (-Complex.I * (Real.pi / 8)) *
              firstDerivativeOscillation (hardyOscillatoryPhase n) t)
        (Set.uIcc T (2 * T)) := by
      intro t ht
      rw [Set.uIcc_of_le hTle] at ht
      have htpos : 0 < t := hT.trans_le ht.1
      exact (continuousAt_const.mul
        ((hasDerivAt_firstDerivativeOscillation
          (hasDerivAt_hardyOscillatoryPhase hn htpos)).continuousAt)).continuousWithinAt
    exact hcont.intervalIntegrable
  calc
    _ = ∫ t in T..2 * T,
        ∑ n ∈ Finset.Icc 1 m,
          (((1 / Real.sqrt n : Real) : Complex) *
            Complex.exp (-Complex.I * (Real.pi / 8)) *
              firstDerivativeOscillation (hardyOscillatoryPhase n) t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hTle] at ht
      simp only
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hnmem
      exact exp_stirlingPhase_mul_cpow_eq_hardyOscillatoryMode
        (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hnmem).1)
        (hT.trans_le ht.1)
    _ = ∑ n ∈ Finset.Icc 1 m,
        ∫ t in T..2 * T,
          ((1 / Real.sqrt n : Real) : Complex) *
            Complex.exp (-Complex.I * (Real.pi / 8)) *
              firstDerivativeOscillation (hardyOscillatoryPhase n) t := by
      apply intervalIntegral.integral_finsetSum
      exact hint
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hnmem
      rw [hardyOscillatoryModeIntegral,
        ← intervalIntegral.integral_const_mul]

/-- The critical-line xi factor divided by its norm is a unit complex
number. -/
theorem norm_hardyXiFactor_unit (t : Real) :
    ‖hardyXiFactor (criticalLinePoint t) /
        ‖hardyXiFactor (criticalLinePoint t)‖‖ = 1 := by
  rw [norm_div]
  have hnorm : ‖hardyXiFactor (criticalLinePoint t)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hardyXiFactor_ne_zero t)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact div_self hnorm

/-- Pointwise H4C approximation: after adding the phased H1 cutoff, the
Hardy function is bounded by the H1 remainder plus the H2 phase error. -/
theorem norm_hardyFunction_add_phased_cutoffSum_le
    {K T t : Real} (hT : 1 ≤ T)
    (ht : T ≤ t)
    (happrox :
      ‖riemannZeta (criticalLinePoint t) -
        ∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
          (n : Complex) ^ (-criticalLinePoint t)‖ ≤ K / Real.sqrt T) :
    ‖hardyFunction t +
        Complex.exp (Complex.I * criticalLineStirlingPhase t) *
          ∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
            (n : Complex) ^ (-criticalLinePoint t)‖ ≤
      (K + 2) / Real.sqrt T := by
  let U : Complex := hardyXiFactor (criticalLinePoint t) /
    ‖hardyXiFactor (criticalLinePoint t)‖
  let E : Complex := Complex.exp
    (Complex.I * criticalLineStirlingPhase t)
  let D : Complex := ∑ n ∈ Finset.Icc 1
    (zetaFirstApproximationCutoff T),
      (n : Complex) ^ (-criticalLinePoint t)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have htone : 1 ≤ t := hT.trans ht
  have hU : ‖U‖ = 1 := by
    exact norm_hardyXiFactor_unit t
  have hm : (zetaFirstApproximationCutoff T : Real) ≤ T :=
    zetaFirstApproximationCutoff_le_height hTpos.le
  have hD : ‖D‖ ≤ 2 * Real.sqrt T := by
    exact (norm_sum_Icc_cpow_neg_criticalLinePoint_le
      (zetaFirstApproximationCutoff T) t).trans (by
        gcongr)
  have hphaseRaw : ‖U + E‖ ≤ 11 / (16 * t) := by
    exact norm_hardyXiFactor_unit_add_exp_stirlingPhase_le htone
  have hphase : ‖U + E‖ ≤ 1 / T := by
    apply hphaseRaw.trans
    calc
      11 / (16 * t) = (11 / 16 : Real) * (1 / t) := by ring
      _ ≤ 1 * (1 / t) := by
        gcongr
        norm_num
      _ = 1 / t := by ring
      _ ≤ 1 / T := one_div_le_one_div_of_le hTpos ht
  have hsqrtPos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hphaseError : ‖(U + E) * D‖ ≤ 2 / Real.sqrt T := by
    calc
      _ = ‖U + E‖ * ‖D‖ := norm_mul _ _
      _ ≤ (1 / T) * (2 * Real.sqrt T) := by
        exact mul_le_mul hphase hD (norm_nonneg D) (by positivity)
      _ = 2 / Real.sqrt T := by
        field_simp [hsqrtPos.ne']
        rw [Real.sq_sqrt hTpos.le]
  have hmainError :
      ‖U * (riemannZeta (criticalLinePoint t) - D)‖ ≤
        K / Real.sqrt T := by
    rw [norm_mul, hU, one_mul]
    exact happrox
  rw [hardyFunction_eq_factor_unit_mul_riemannZeta]
  change ‖U * riemannZeta (criticalLinePoint t) + E * D‖ ≤ _
  calc
    _ = ‖U * (riemannZeta (criticalLinePoint t) - D) +
        (U + E) * D‖ := by
      congr 1
      ring
    _ ≤ ‖U * (riemannZeta (criticalLinePoint t) - D)‖ +
        ‖(U + E) * D‖ := norm_add_le _ _
    _ ≤ K / Real.sqrt T + 2 / Real.sqrt T :=
      add_le_add hmainError hphaseError
    _ = (K + 2) / Real.sqrt T := by ring

/-- The phased cutoff sum is interval-integrable on every positive dyadic
interval. -/
theorem intervalIntegrable_exp_stirlingPhase_mul_cutoffSum
    {m : Nat} {T : Real} (hT : 0 < T) :
    IntervalIntegrable
      (fun t : Real =>
        Complex.exp (Complex.I * criticalLineStirlingPhase t) *
          ∑ n ∈ Finset.Icc 1 m,
            (n : Complex) ^ (-criticalLinePoint t)) volume T (2 * T) := by
  have hTle : T ≤ 2 * T := by linarith
  let G : Real → Complex := fun t =>
    ∑ n ∈ Finset.Icc 1 m,
      ((1 / Real.sqrt n : Real) : Complex) *
        Complex.exp (-Complex.I * (Real.pi / 8)) *
          firstDerivativeOscillation (hardyOscillatoryPhase n) t
  have hGcont : ContinuousOn G (Set.uIcc T (2 * T)) := by
    dsimp only [G]
    apply continuousOn_finsetSum
    intro n hnmem
    have hn : 0 < n :=
      lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hnmem).1
    intro t ht
    rw [Set.uIcc_of_le hTle] at ht
    exact (continuousAt_const.mul
      ((hasDerivAt_firstDerivativeOscillation
        (hasDerivAt_hardyOscillatoryPhase hn (hT.trans_le ht.1))).continuousAt)).continuousWithinAt
  apply hGcont.intervalIntegrable.congr
  intro t ht
  rw [uIoc_of_le hTle] at ht
  dsimp only [G]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hnmem
  exact (exp_stirlingPhase_mul_cpow_eq_hardyOscillatoryMode
    (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hnmem).1)
    (hT.trans_le (le_of_lt ht.1))).symm

/-- Integrating the combined H1/H2 approximation error costs exactly the
dyadic interval length. -/
theorem norm_integral_hardyFunction_add_phased_cutoffSum_le
    {K T : Real} (hT : 1 ≤ T)
    (happrox : ∀ t : Real, T ≤ t → t ≤ 2 * T →
      ‖riemannZeta (criticalLinePoint t) -
        ∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
          (n : Complex) ^ (-criticalLinePoint t)‖ ≤ K / Real.sqrt T) :
    ‖∫ t in T..2 * T,
        (hardyFunction t +
          Complex.exp (Complex.I * criticalLineStirlingPhase t) *
            ∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
              (n : Complex) ^ (-criticalLinePoint t))‖ ≤
      (K + 2) * Real.sqrt T := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hTle : T ≤ 2 * T := by linarith
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := T) (b := 2 * T) (C := (K + 2) / Real.sqrt T)
    (f := fun t : Real =>
      hardyFunction t +
        Complex.exp (Complex.I * criticalLineStirlingPhase t) *
          ∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
            (n : Complex) ^ (-criticalLinePoint t))
    (fun t ht => by
      rw [uIoc_of_le hTle] at ht
      exact norm_hardyFunction_add_phased_cutoffSum_le hT
        (le_of_lt ht.1) (happrox t (le_of_lt ht.1) ht.2))
  have hsqrtPos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  calc
    _ ≤ ((K + 2) / Real.sqrt T) * |2 * T - T| := hbound
    _ = ((K + 2) / Real.sqrt T) * T := by
      rw [abs_of_pos (by linarith)]
      ring
    _ = (K + 2) * Real.sqrt T := by
      field_simp [hsqrtPos.ne']
      rw [Real.sq_sqrt hTpos.le]

/-- Quantitative complex H4C upper bound before transferring back to the
real Hardy presentation. -/
theorem norm_integral_hardyFunction_le
    {K T : Real} (hK : 0 < K) (hT : 1 ≤ T)
    (happrox : ∀ t : Real, T ≤ t → t ≤ 2 * T →
      ‖riemannZeta (criticalLinePoint t) -
        ∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
          (n : Complex) ^ (-criticalLinePoint t)‖ ≤ K / Real.sqrt T) :
    ‖∫ t in T..2 * T, hardyFunction t‖ ≤
      (K + 100) * T ^ (3 / 4 : Real) := by
  let M : Real → Complex := fun t =>
    Complex.exp (Complex.I * criticalLineStirlingPhase t) *
      ∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
        (n : Complex) ^ (-criticalLinePoint t)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hH : IntervalIntegrable hardyFunction volume T (2 * T) :=
    continuous_hardyFunction.intervalIntegrable _ _
  have hM : IntervalIntegrable M volume T (2 * T) := by
    dsimp only [M]
    exact intervalIntegrable_exp_stirlingPhase_mul_cutoffSum hTpos
  have hadd := intervalIntegral.integral_add hH hM
  have herror : ‖∫ t in T..2 * T, (hardyFunction t + M t)‖ ≤
      (K + 2) * Real.sqrt T := by
    dsimp only [M]
    exact norm_integral_hardyFunction_add_phased_cutoffSum_le hT happrox
  have hmain : ‖∫ t in T..2 * T, M t‖ ≤
      98 * T ^ (3 / 4 : Real) := by
    rw [show (∫ t in T..2 * T, M t) =
        ∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
          hardyOscillatoryModeIntegral n T by
      dsimp only [M]
      exact integral_exp_stirlingPhase_mul_cutoffSum_eq hTpos]
    exact norm_sum_cutoff_hardyOscillatoryModeIntegral_le hT
  have hsqrtOne : 1 ≤ Real.sqrt T := by
    simpa using Real.sqrt_le_sqrt hT
  have hsqrtSqrtOne : 1 ≤ Real.sqrt (Real.sqrt T) := by
    simpa using Real.sqrt_le_sqrt hsqrtOne
  have hsqrt_le_scale : Real.sqrt T ≤ T ^ (3 / 4 : Real) := by
    calc
      Real.sqrt T = Real.sqrt T * 1 := by ring
      _ ≤ Real.sqrt T * Real.sqrt (Real.sqrt T) := by gcongr
      _ = T ^ (3 / 4 : Real) :=
        sqrt_mul_sqrt_sqrt_eq_rpow_three_quarters hTpos
  calc
    ‖∫ t in T..2 * T, hardyFunction t‖ =
        ‖(∫ t in T..2 * T, (hardyFunction t + M t)) -
          ∫ t in T..2 * T, M t‖ := by
      rw [hadd]
      congr 1
      ring
    _ ≤ ‖∫ t in T..2 * T, (hardyFunction t + M t)‖ +
        ‖∫ t in T..2 * T, M t‖ := norm_sub_le _ _
    _ ≤ (K + 2) * Real.sqrt T +
        98 * T ^ (3 / 4 : Real) := add_le_add herror hmain
    _ ≤ (K + 2) * T ^ (3 / 4 : Real) +
        98 * T ^ (3 / 4 : Real) := by
      gcongr
    _ = (K + 100) * T ^ (3 / 4 : Real) := by ring

/-- The real Hardy integral has the norm of its complex presentation. -/
theorem abs_integral_hardyFunctionReal_eq_norm (T : Real) :
    |∫ t in T..2 * T, hardyFunctionReal t| =
      ‖∫ t in T..2 * T, hardyFunction t‖ := by
  have heq :
      ((∫ t in T..2 * T, hardyFunctionReal t : Real) : Complex) =
        ∫ t in T..2 * T, hardyFunction t := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _
    exact ofReal_hardyFunctionReal_eq t
  have hnorm := congrArg norm heq
  simpa [Complex.norm_real, Real.norm_eq_abs] using hnorm

/-- H4C: beyond a fixed threshold, the signed Hardy integral on `[T, 2T]`
has an explicit `T^(3/4)` upper bound. -/
theorem exists_hardyUpperIntegralBound :
    ∃ Cupper T₁ : Real, 0 < Cupper ∧ 2 ≤ T₁ ∧
      ∀ T : Real, T₁ ≤ T →
        |∫ t in T..2 * T, hardyFunctionReal t| ≤
          Cupper * T ^ (3 / 4 : Real) := by
  obtain ⟨K, hK, T₀, hT₀, happrox⟩ :=
    exists_uniform_zetaFirstApproximation
  refine ⟨K + 100, T₀, by linarith, hT₀, ?_⟩
  intro T hT
  have hTone : 1 ≤ T := (by norm_num : (1 : Real) ≤ 2).trans
    (hT₀.trans hT)
  have happrox' : ∀ t : Real, T ≤ t → t ≤ 2 * T →
      ‖riemannZeta (criticalLinePoint t) -
        ∑ n ∈ Finset.Icc 1 (zetaFirstApproximationCutoff T),
          (n : Complex) ^ (-criticalLinePoint t)‖ ≤ K / Real.sqrt T := by
    intro t ht ht'
    have happ := happrox T t hT ht ht'
    norm_num [criticalLinePoint] at happ ⊢
    exact happ
  rw [abs_integral_hardyFunctionReal_eq_norm]
  exact norm_integral_hardyFunction_le hK hTone happrox'

end

end Hardy

end RiemannHypothesisProject
