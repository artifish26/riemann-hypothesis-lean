import RiemannHypothesisProject.GuinandWeilConcrete.Sides

/-!
# Prime-side cutoff facts for concrete Guinand-Weil formulae

This module contains prime-term arithmetic facts, Fourier compact-support
vanishing, prime-side summability, and finite-cutoff stabilization for the
concrete Guinand-Weil formula route.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

/--
On an actual prime, the concrete prime component has the classical
`log p / sqrt p` coefficient.
-/
theorem guinandWeilPrimeTerm_of_prime
    (f : SchwartzLineTestFunction)
    {p : Nat} (hp : p.Prime) :
    guinandWeilPrimeTerm f p =
      - (Real.log (p : Real) / Real.sqrt (p : Real)) *
        (((SchwartzLineTestFunction.fourier f) (Real.log (p : Real))).re +
          ((SchwartzLineTestFunction.fourier f) (-Real.log (p : Real))).re) := by
  unfold guinandWeilPrimeTerm
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Away from prime powers, the concrete prime component is exactly zero. -/
theorem guinandWeilPrimeTerm_eq_zero_of_not_primePow
    (f : SchwartzLineTestFunction)
    {n : Nat} (hn : Not (IsPrimePow n)) :
    guinandWeilPrimeTerm f n = 0 := by
  unfold guinandWeilPrimeTerm
  rw [(ArithmeticFunction.vonMangoldt_eq_zero_iff).mpr hn]
  ring

/--
On a genuine prime power, the concrete prime component still carries the
underlying prime's logarithm, as the von Mangoldt function requires.
-/
theorem guinandWeilPrimeTerm_of_prime_pow
    (f : SchwartzLineTestFunction)
    {p k : Nat} (hp : p.Prime) (hk : k ≠ 0) :
    guinandWeilPrimeTerm f (p ^ k) =
      - (Real.log (p : Real) / Real.sqrt ((p ^ k : Nat) : Real)) *
        (((SchwartzLineTestFunction.fourier f)
            (Real.log (((p ^ k : Nat) : Real)))).re +
          ((SchwartzLineTestFunction.fourier f)
            (-Real.log (((p ^ k : Nat) : Real)))).re) := by
  unfold guinandWeilPrimeTerm
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- A nonzero concrete prime component can only come from a prime power. -/
theorem isPrimePow_of_guinandWeilPrimeTerm_ne_zero
    (f : SchwartzLineTestFunction)
    {n : Nat} (hterm : guinandWeilPrimeTerm f n ≠ 0) :
    IsPrimePow n := by
  by_contra hn
  exact hterm (guinandWeilPrimeTerm_eq_zero_of_not_primePow f hn)

/--
An explicit compact Fourier support radius kills a prime summand as soon as the
logarithmic sample is outside that radius.
-/
theorem guinandWeilPrimeTerm_eq_zero_of_fourierSupportRadius_lt_log
    (f : SchwartzLineTestFunction)
    {R : Real} (_hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    {n : Nat} (hlog : R < Real.log (n : Real)) :
    guinandWeilPrimeTerm f n = 0 := by
  have hlog_abs : R < |Real.log (n : Real)| :=
    hlog.trans_le (le_abs_self (Real.log (n : Real)))
  have hneg_log_abs : R < |-Real.log (n : Real)| := by
    simpa only [abs_neg] using hlog_abs
  have hplus :
      SchwartzLineTestFunction.fourier f (Real.log (n : Real)) = 0 :=
    hsupport (Real.log (n : Real)) hlog_abs
  have hminus :
      SchwartzLineTestFunction.fourier f (-Real.log (n : Real)) = 0 :=
    hsupport (-Real.log (n : Real)) hneg_log_abs
  simp [guinandWeilPrimeTerm, hplus, hminus]

/-- Compact Fourier support makes the concrete prime summand eventually zero. -/
theorem eventually_guinandWeilPrimeTerm_eq_zero_of_fourierCompactSupport
    (f : SchwartzLineTestFunction)
    (hf : GuinandWeilFourierCompactSupport f) :
    ∀ᶠ n : Nat in atTop, guinandWeilPrimeTerm f n = 0 := by
  rcases hf with ⟨R, _hR_nonneg, hsupport⟩
  have hlog :
      Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := Real))
  filter_upwards [hlog.eventually_gt_atTop R] with n hn
  have hlog_abs : R < |Real.log (n : Real)| :=
    hn.trans_le (le_abs_self (Real.log (n : Real)))
  have hneg_log_abs : R < |-Real.log (n : Real)| := by
    simpa only [abs_neg] using hlog_abs
  have hplus :
      SchwartzLineTestFunction.fourier f (Real.log (n : Real)) = 0 :=
    hsupport (Real.log (n : Real)) hlog_abs
  have hminus :
      SchwartzLineTestFunction.fourier f (-Real.log (n : Real)) = 0 :=
    hsupport (-Real.log (n : Real)) hneg_log_abs
  simp [guinandWeilPrimeTerm, hplus, hminus]

/-- Any eventually-zero concrete prime summand is summable. -/
theorem summable_guinandWeilPrimeTerm_of_eventually_eq_zero
    (f : SchwartzLineTestFunction)
    (hzero : ∀ᶠ n : Nat in atTop, guinandWeilPrimeTerm f n = 0) :
    Summable (fun n : Nat => guinandWeilPrimeTerm f n) := by
  rcases eventually_atTop.1 hzero with ⟨N, hN⟩
  refine summable_of_ne_finset_zero (s := Finset.range N) ?_
  intro n hn
  have hnge : N <= n := by
    rw [Finset.mem_range] at hn
    exact Nat.le_of_not_gt hn
  exact hN n hnge

/--
Compact Fourier support supplies the concrete prime-side summability hypothesis
needed by the finite-error Guinand-Weil source theorem.
-/
theorem summable_guinandWeilPrimeTerm_of_fourierCompactSupport
    (f : SchwartzLineTestFunction)
    (hf : GuinandWeilFourierCompactSupport f) :
    Summable (fun n : Nat => guinandWeilPrimeTerm f n) :=
  summable_guinandWeilPrimeTerm_of_eventually_eq_zero f
    (eventually_guinandWeilPrimeTerm_eq_zero_of_fourierCompactSupport f hf)

/--
With an explicit compact Fourier support radius and a cutoff whose tail log
samples are outside that radius, the limiting prime side is a finite cutoff
sum.
-/
theorem guinandWeilPrimeSide_eq_sum_Icc_of_fourierSupportRadius
    (f : SchwartzLineTestFunction)
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (cutoff : Nat)
    (hcutoff :
      ∀ n : Nat, cutoff < n -> R < Real.log (n : Real)) :
    guinandWeilPrimeSide f =
      (Finset.Icc 1 cutoff).sum (fun n : Nat => guinandWeilPrimeTerm f n) := by
  unfold guinandWeilPrimeSide
  exact tsum_eq_sum (s := Finset.Icc 1 cutoff) (fun n hn => by
    by_cases hn_zero : n = 0
    · subst n
      simp [guinandWeilPrimeTerm]
    · have hn_one : 1 <= n := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hn_zero)
      have hn_not_mem : ¬ (1 <= n ∧ n <= cutoff) := by
        simpa [Finset.mem_Icc] using hn
      have hn_not_le : ¬ n <= cutoff := fun hn_le => hn_not_mem ⟨hn_one, hn_le⟩
      have hcutoff_lt : cutoff < n := Nat.lt_of_not_ge hn_not_le
      exact
        guinandWeilPrimeTerm_eq_zero_of_fourierSupportRadius_lt_log
          f hR_nonneg hsupport (hcutoff n hcutoff_lt))

/--
The numeric cutoff condition `exp R < cutoff + 1` is enough to make all tail
log samples clear the explicit compact Fourier support radius.
-/
theorem guinandWeilPrimeSide_eq_sum_Icc_of_fourierSupportRadius_exp_lt_succ
    (f : SchwartzLineTestFunction)
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (cutoff : Nat)
    (hcutoff : Real.exp R < ((cutoff + 1 : Nat) : Real)) :
    guinandWeilPrimeSide f =
      (Finset.Icc 1 cutoff).sum (fun n : Nat => guinandWeilPrimeTerm f n) :=
  guinandWeilPrimeSide_eq_sum_Icc_of_fourierSupportRadius
    f hR_nonneg hsupport cutoff (fun n hn => by
      have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le cutoff) hn
      have hn_real_pos : 0 < (n : Real) := Nat.cast_pos.mpr hn_pos
      have hsucc_le : cutoff + 1 <= n := Nat.succ_le_iff.mpr hn
      have hsucc_le_real : ((cutoff + 1 : Nat) : Real) <= (n : Real) := by
        exact_mod_cast hsucc_le
      have hexp_lt_n : Real.exp R < (n : Real) :=
        hcutoff.trans_le hsucc_le_real
      exact (Real.lt_log_iff_exp_lt hn_real_pos).2 hexp_lt_n)

/--
The concrete truncated prime side is exactly the limiting prime side once the
cutoff is beyond the explicit compact Fourier support radius.
-/
theorem guinandWeilTruncatedPrimeSide_eq_primeSide_of_fourierSupportRadius
    (f : SchwartzLineTestFunction)
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (cutoff : Nat)
    (hcutoff :
      ∀ n : Nat, cutoff < n -> R < Real.log (n : Real)) :
    guinandWeilTruncatedPrimeSide cutoff f = guinandWeilPrimeSide f := by
  rw [guinandWeilPrimeSide_eq_sum_Icc_of_fourierSupportRadius
    f hR_nonneg hsupport cutoff hcutoff]
  rfl

/--
The concrete truncated prime side is exactly the limiting prime side whenever
the cutoff exceeds the exponential of the explicit compact Fourier support
radius.
-/
theorem guinandWeilTruncatedPrimeSide_eq_primeSide_of_fourierSupportRadius_exp_lt_succ
    (f : SchwartzLineTestFunction)
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (cutoff : Nat)
    (hcutoff : Real.exp R < ((cutoff + 1 : Nat) : Real)) :
    guinandWeilTruncatedPrimeSide cutoff f = guinandWeilPrimeSide f := by
  rw [guinandWeilPrimeSide_eq_sum_Icc_of_fourierSupportRadius_exp_lt_succ
    f hR_nonneg hsupport cutoff hcutoff]
  rfl

/-- Every fixed Fourier support radius is eventually below `cutoff + 1`. -/
theorem eventually_fourierSupportRadius_exp_lt_succ
    (R : Real) :
    ∀ᶠ cutoff : Nat in atTop,
      Real.exp R < ((cutoff + 1 : Nat) : Real) := by
  have hnat :
      Tendsto (fun cutoff : Nat => (cutoff : Real) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1
      tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually_gt_atTop (Real.exp R)] with cutoff hcutoff
  simpa [Nat.cast_add, Nat.cast_one] using hcutoff

/-- At cutoff zero the truncated prime side is empty. -/
@[simp]
theorem guinandWeilTruncatedPrimeSide_zero
    (f : SchwartzLineTestFunction) :
    guinandWeilTruncatedPrimeSide 0 f = 0 := by
  simp [guinandWeilTruncatedPrimeSide]

/-- Prime cutoff membership is exactly the expected numeric interval. -/
theorem mem_guinandWeilPrimeCutoff_iff
    {cutoff n : Nat} :
    n ∈ Finset.Icc 1 cutoff <-> 1 <= n /\ n <= cutoff := by
  simp

/-- The prime component is zero at the artificial Nat index `0`. -/
@[simp]
theorem guinandWeilPrimeTerm_zero
    (f : SchwartzLineTestFunction) :
    guinandWeilPrimeTerm f 0 = 0 := by
  unfold guinandWeilPrimeTerm
  simp

/--
The usual `range (cutoff + 1)` partial sum agrees with the positive-indexed
prime cutoff because the `0`th prime component is zero.
-/
theorem guinandWeilPrimeRangeSum_eq_truncatedPrimeSide
    (cutoff : Nat)
    (f : SchwartzLineTestFunction) :
    (Finset.range (cutoff + 1)).sum (fun n : Nat => guinandWeilPrimeTerm f n) =
      guinandWeilTruncatedPrimeSide cutoff f := by
  rw [Nat.range_succ_eq_Icc_zero]
  rw [Finset.Icc_eq_cons_Ioc cutoff.zero_le, Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  simp [guinandWeilTruncatedPrimeSide]

/--
If the concrete prime summand is eventually zero, the positive-indexed
truncated prime side is eventually exactly the limiting prime side.
-/
theorem eventually_guinandWeilTruncatedPrimeSide_eq_primeSide_of_eventually_eq_zero
    (f : SchwartzLineTestFunction)
    (hzero : ∀ᶠ n : Nat in atTop, guinandWeilPrimeTerm f n = 0) :
    ∀ᶠ cutoff : Nat in atTop,
      guinandWeilTruncatedPrimeSide cutoff f = guinandWeilPrimeSide f := by
  rcases eventually_atTop.1 hzero with ⟨N, hN⟩
  have htsum :
      guinandWeilPrimeSide f =
        (Finset.range N).sum (fun n : Nat => guinandWeilPrimeTerm f n) := by
    rw [guinandWeilPrimeSide]
    exact tsum_eq_sum (s := Finset.range N) (fun n hn => by
      have hnge : N <= n := by
        rw [Finset.mem_range] at hn
        exact Nat.le_of_not_gt hn
      exact hN n hnge)
  filter_upwards [eventually_ge_atTop N] with cutoff hcutoff
  have hsubset : Finset.range N ⊆ Finset.range (cutoff + 1) := by
    intro n hn
    rw [Finset.mem_range] at hn ⊢
    exact hn.trans_le (Nat.le_succ_of_le hcutoff)
  have hsum :
      (Finset.range (cutoff + 1)).sum
          (fun n : Nat => guinandWeilPrimeTerm f n) =
        (Finset.range N).sum (fun n : Nat => guinandWeilPrimeTerm f n) := by
    exact (Finset.sum_subset hsubset (fun n _hn_big hn_small => by
      have hnge : N <= n := by
        rw [Finset.mem_range] at hn_small
        exact Nat.le_of_not_gt hn_small
      exact hN n hnge)).symm
  rw [← guinandWeilPrimeRangeSum_eq_truncatedPrimeSide cutoff f, hsum, htsum]

/--
Compact Fourier support makes the positive-indexed truncated prime side
eventually stabilize to the limiting prime side.
-/
theorem eventually_guinandWeilTruncatedPrimeSide_eq_primeSide_of_fourierCompactSupport
    (f : SchwartzLineTestFunction)
    (hf : GuinandWeilFourierCompactSupport f) :
    ∀ᶠ cutoff : Nat in atTop,
      guinandWeilTruncatedPrimeSide cutoff f = guinandWeilPrimeSide f :=
  eventually_guinandWeilTruncatedPrimeSide_eq_primeSide_of_eventually_eq_zero f
    (eventually_guinandWeilPrimeTerm_eq_zero_of_fourierCompactSupport f hf)

end

end RiemannHypothesisProject
