import RiemannHypothesisProject.Hardy.UpperIntegralBound

/-!
# Infinitely many critical-line zeta zeros

This module is the H4D endpoint.  It combines continuity and zero equivalence
from H4A with the lower absolute-integral bound from H4B and the upper signed-
integral bound from H4C.  No further analytic source theorem is used.
-/

open Complex MeasureTheory Set

namespace RiemannHypothesisProject

namespace Hardy

noncomputable section

/-- Positive heights at which the real Hardy function vanishes. -/
def positiveHardyZeroHeights : Set Real :=
  {t : Real | 0 < t ∧ hardyFunctionReal t = 0}

/-- A continuous nonvanishing real function has a constant weak sign on an
interval. -/
theorem nonnegative_or_nonpositive_on_Icc_of_continuous_ne_zero
    {f : Real → Real} (hf : Continuous f) {a b : Real} (hab : a ≤ b)
    (hne : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    (∀ x ∈ Set.Icc a b, 0 ≤ f x) ∨
      (∀ x ∈ Set.Icc a b, f x ≤ 0) := by
  have hne_a : f a ≠ 0 := hne a ⟨le_rfl, hab⟩
  rcases lt_or_gt_of_ne hne_a with ha_neg | ha_pos
  · right
    intro x hx
    by_contra hx_not
    have hx_pos : 0 < f x := lt_of_not_ge hx_not
    have hzero_mem : (0 : Real) ∈ Set.Icc (f a) (f x) := ⟨ha_neg.le, hx_pos.le⟩
    rcases (intermediate_value_Icc hx.1 hf.continuousOn) hzero_mem with
      ⟨y, hy, hy_zero⟩
    exact hne y ⟨hy.1, hy.2.trans hx.2⟩ hy_zero
  · left
    intro x hx
    by_contra hx_not
    have hx_neg : f x < 0 := lt_of_not_ge hx_not
    have hzero_mem : (0 : Real) ∈ Set.Icc (f x) (f a) := ⟨hx_neg.le, ha_pos.le⟩
    rcases (intermediate_value_Icc' hx.1 hf.continuousOn) hzero_mem with
      ⟨y, hy, hy_zero⟩
    exact hne y ⟨hy.1, hy.2.trans hx.2⟩ hy_zero

/-- On an interval where a real function has one weak sign, the magnitude of
its signed integral is its absolute-value integral. -/
theorem abs_integral_eq_integral_abs_of_constant_sign
    {f : Real → Real} {a b : Real} (hab : a ≤ b)
    (hsign : (∀ x ∈ Set.Icc a b, 0 ≤ f x) ∨
      (∀ x ∈ Set.Icc a b, f x ≤ 0)) :
    |∫ x in a..b, f x| = ∫ x in a..b, |f x| := by
  rcases hsign with hnonneg | hnonpos
  · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hab hnonneg)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (abs_of_nonneg (hnonneg x hx)).symm
  · have hneg_nonneg : 0 ≤ ∫ x in a..b, -f x :=
      intervalIntegral.integral_nonneg hab fun x hx => neg_nonneg.mpr (hnonpos x hx)
    rw [intervalIntegral.integral_neg] at hneg_nonneg
    rw [abs_of_nonpos (by linarith : (∫ x in a..b, f x) ≤ 0)]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (abs_of_nonpos (hnonpos x hx)).symm

/-- If the positive Hardy zero heights were finite, every sufficiently late
dyadic interval would have the signed/absolute integral identity. -/
theorem eventually_abs_integral_hardyFunctionReal_eq_integral_abs
    (hfinite : positiveHardyZeroHeights.Finite) :
    ∃ T₀ : Real, 2 ≤ T₀ ∧ ∀ T : Real, T₀ ≤ T →
      |∫ t in T..2 * T, hardyFunctionReal t| =
        ∫ t in T..2 * T, |hardyFunctionReal t| := by
  rcases hfinite.bddAbove with ⟨B, hB⟩
  let T₀ : Real := max 2 (B + 1)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hT)
  have htwoT : T ≤ 2 * T := by linarith
  have hne : ∀ t ∈ Set.Icc T (2 * T), hardyFunctionReal t ≠ 0 := by
    intro t ht hzero
    have htpos : 0 < t := hTpos.trans_le ht.1
    have htB : t ≤ B := hB ⟨htpos, hzero⟩
    have hB1 : B + 1 ≤ t := (le_max_right _ _).trans hT |>.trans ht.1
    linarith
  exact abs_integral_eq_integral_abs_of_constant_sign htwoT
    (nonnegative_or_nonpositive_on_Icc_of_continuous_ne_zero
      continuous_hardyFunctionReal htwoT hne)

/-- The positive real zero heights of Hardy's function are infinite. -/
theorem positiveHardyZeroHeights_infinite :
    positiveHardyZeroHeights.Infinite := by
  by_contra hnotInfinite
  have hfinite : positiveHardyZeroHeights.Finite := Set.not_infinite.mp hnotInfinite
  obtain ⟨Tsign, hTsign, hsign⟩ :=
    eventually_abs_integral_hardyFunctionReal_eq_integral_abs hfinite
  obtain ⟨Tlower, hTlower, hlower⟩ := exists_hardyLowerIntegralBound
  obtain ⟨Cupper, Tupper, hCupper, hTupper, hupper⟩ :=
    exists_hardyUpperIntegralBound
  let scale : Real := 4 * Cupper ^ 2
  let T : Real := max (max Tsign (max Tlower Tupper)) (scale ^ 2 + 1)
  have hTsignT : Tsign ≤ T :=
    (le_max_left Tsign (max Tlower Tupper)).trans (le_max_left _ _)
  have hTlowerT : Tlower ≤ T :=
    (le_max_left Tlower Tupper).trans (le_max_right Tsign (max Tlower Tupper)) |>
      fun h => h.trans (le_max_left _ _)
  have hTupperT : Tupper ≤ T :=
    (le_max_right Tlower Tupper).trans (le_max_right Tsign (max Tlower Tupper)) |>
      fun h => h.trans (le_max_left _ _)
  have hTtwo : 2 ≤ T := hTsign.trans hTsignT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTtwo
  have hlarge : scale ^ 2 < T := by
    have : scale ^ 2 + 1 ≤ T := le_max_right _ _
    linarith
  have hsqrt_sq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTpos.le
  have hsqrt_nonneg : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hscale_nonneg : 0 ≤ scale := by
    dsimp only [scale]
    positivity
  have hscale_sqrt : scale < Real.sqrt T := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hsqrtSqrt_sq : Real.sqrt (Real.sqrt T) ^ 2 = Real.sqrt T :=
    Real.sq_sqrt hsqrt_nonneg
  have hsqrtSqrt_nonneg : 0 ≤ Real.sqrt (Real.sqrt T) := Real.sqrt_nonneg _
  have htwoC_nonneg : 0 ≤ 2 * Cupper := by positivity
  have htwoC_sqrt_lt :
      2 * Cupper * Real.sqrt (Real.sqrt T) < Real.sqrt T := by
    dsimp only [scale] at hscale_sqrt
    nlinarith
  have hgrowth :
      Cupper * (Real.sqrt T * Real.sqrt (Real.sqrt T)) < T / 2 := by
    nlinarith
  have hscale_eq :
      Real.sqrt T * Real.sqrt (Real.sqrt T) = T ^ (3 / 4 : Real) :=
    sqrt_mul_sqrt_sqrt_eq_rpow_three_quarters hTpos
  have hupperT := hupper T hTupperT
  have hlowerT := hlower T hTlowerT
  have hsignT := hsign T hTsignT
  rw [hsignT] at hupperT
  rw [← hscale_eq] at hupperT
  linarith

/-- The critical-line parametrization is injective. -/
theorem criticalLinePoint_injective : Function.Injective criticalLinePoint := by
  intro t u htu
  have him := congrArg Complex.im htu
  simpa [criticalLinePoint] using him

/-- Every positive Hardy zero height gives an actual nontrivial zeta zero on
the critical line. -/
theorem criticalLinePoint_mem_nontrivial_criticalLine_zero_set
    {t : Real} (ht : t ∈ positiveHardyZeroHeights) :
    criticalLinePoint t ∈
      {s : Complex | IsNontrivialZetaZero s ∧ IsCriticalLine s} := by
  have hzeta : riemannZeta (criticalLinePoint t) = 0 :=
    (hardyFunctionReal_eq_zero_iff t).mp ht.2
  have hnotTrivial : ¬ IsTrivialZetaZero (criticalLinePoint t) := by
    rintro ⟨n, hn⟩
    have him := congrArg Complex.im hn
    norm_num [criticalLinePoint] at him
    exact ht.1.ne' him
  have hneOne : criticalLinePoint t ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    norm_num [criticalLinePoint] at hre
  exact ⟨⟨hzeta, hnotTrivial, hneOne⟩, criticalLinePoint_on_line t⟩

/-- H4D: the set of actual nontrivial zeta zeros on the critical line is
infinite. -/
theorem nontrivial_criticalLine_zetaZero_set_infinite :
    {s : Complex | IsNontrivialZetaZero s ∧ IsCriticalLine s}.Infinite := by
  have himage : (criticalLinePoint '' positiveHardyZeroHeights).Infinite :=
    positiveHardyZeroHeights_infinite.image criticalLinePoint_injective.injOn
  exact himage.mono fun s hs => by
    rcases hs with ⟨t, ht, rfl⟩
    exact criticalLinePoint_mem_nontrivial_criticalLine_zero_set ht

end

end Hardy

end RiemannHypothesisProject
