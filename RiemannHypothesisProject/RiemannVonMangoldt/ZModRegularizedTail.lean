import RiemannHypothesisProject.RiemannVonMangoldt.ZModAdditiveCharacter

/-!
# ZMod regularized Hurwitz-tail bridges

This module contains complete-period block comparisons, regularized Hurwitz-tail identities, L-function bridges, Abel-integral formulas, and source-shaped ZMod boundary-value theorem surfaces.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section
/--
One full period block of the additive-character `LSeries.term` coefficients.

The block indexed by `m` contains the terms
`m * N + 1, ..., (m + 1) * N`.  This is the natural zero-mean grouping used to
compare the conditional Dirichlet value with the Hurwitz-zeta continuation.
-/
noncomputable def zmodAdditiveCharacterLSeriesPeriodBlock
    {N : Nat} [NeZero N] (j : ZMod N) (x : Real) (m : Nat) : Complex :=
  ∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
    LSeries.term
      (fun n : Nat => ZMod.stdAddChar (j * (n : ZMod N)))
      (x : Complex) k

/--
Partial sums of full period blocks are exactly the ordinary `LSeries.term`
partial sums at period cutoffs.

This is the finite normalization needed before comparing the conditional
boundary value with the `ZMod.LFunction`/Hurwitz expression: the conditional
series is now grouped into complete zero-mean periods.
-/
theorem zmodAdditiveCharacterLSeriesPeriodBlock_partial_sum_eq_range
    {N : Nat} [NeZero N] (j : ZMod N) (x : Real) (M : Nat) :
    (∑ m ∈ Finset.range M,
      zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m) =
      (Finset.range (M * N + 1)).sum
        (fun k : Nat =>
          LSeries.term
            (fun n : Nat => ZMod.stdAddChar (j * (n : ZMod N)))
            (x : Complex) k) := by
  induction M with
  | zero =>
      simp [zmodAdditiveCharacterLSeriesPeriodBlock, LSeries.term_zero]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih,
        zmodAdditiveCharacterLSeriesPeriodBlock]
      have hle : M * N + 1 ≤ (M + 1) * N + 1 := by
        have hN : 0 < N := NeZero.pos N
        nlinarith
      simpa [Nat.succ_eq_add_one] using
        (Finset.sum_range_add_sum_Ico
          (fun k : Nat =>
            LSeries.term
              (fun n : Nat => ZMod.stdAddChar (j * (n : ZMod N)))
              (x : Complex) k) hle)

/--
The additive-character coefficients have zero sum on every complete period
block.

This is the exact finite cancellation that makes the block-regularized
Dirichlet series decay faster than the ungrouped conditionally convergent
series.
-/
theorem zmodAdditiveCharacterCoeff_periodBlock_sum_eq_zero
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0) (m : Nat) :
    (∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
      ZMod.stdAddChar (j * (k : ZMod N))) = 0 := by
  let c : Nat -> Complex := fun k =>
    if k = 0 then 0 else ZMod.stdAddChar (j * (k : ZMod N))
  have hle : m * N + 1 ≤ (m + 1) * N + 1 := by
    have hN : 0 < N := NeZero.pos N
    nlinarith
  have hstart :
      (Finset.range (m * N + 1)).sum c = 0 := by
    rw [Nat.range_succ_eq_Icc_zero]
    have hmod : (m * N) % N = 0 := Nat.mul_mod_left m N
    simpa [c, hmod] using
      zmodAdditiveCharacterCoeff_Icc_zero_sum_eq_mod
        (N := N) (j := j) hj (m * N)
  have hend :
      (Finset.range ((m + 1) * N + 1)).sum c = 0 := by
    rw [Nat.range_succ_eq_Icc_zero]
    have hmod : ((m + 1) * N) % N = 0 := Nat.mul_mod_left (m + 1) N
    simpa [c, hmod] using
      zmodAdditiveCharacterCoeff_Icc_zero_sum_eq_mod
        (N := N) (j := j) hj ((m + 1) * N)
  have hblock_c :
      (∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1), c k) = 0 := by
    have hsplit :=
      Finset.sum_range_add_sum_Ico (f := c) hle
    rw [hstart, hend] at hsplit
    simpa using hsplit
  calc
    (∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
      ZMod.stdAddChar (j * (k : ZMod N))) =
        ∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1), c k := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk_ne : k ≠ 0 := by
            have hk_pos : 0 < k :=
              (Nat.succ_pos (m * N)).trans_le (Finset.mem_Ico.mp hk).1
            exact ne_of_gt hk_pos
          simp [c, hk_ne]
    _ = 0 := hblock_c

/--
Residue-coordinate zero mean for one complete additive-character period.

This is the finite cancellation used to remove the common Hurwitz pole branch
after the regularized tails are identified with Hurwitz-zeta differences.
-/
theorem zmodAdditiveCharacterCoeff_Ico_one_period_sum_eq_zero
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0) :
    (∑ r ∈ Finset.Ico 1 (N + 1),
      ZMod.stdAddChar (j * (r : ZMod N))) = 0 := by
  simpa using
    zmodAdditiveCharacterCoeff_periodBlock_sum_eq_zero
      (N := N) (j := j) hj 0

/--
Finite reindexing of a `ZMod N` sum by the residue interval `1, ..., N`.

The representative convention sends the zero residue to `N` and every nonzero
residue to its canonical value.  This is the coordinate bridge between the
regularized block route, which naturally uses `Ico 1 (N + 1)`, and Mathlib's
`ZMod.LFunction`, which sums over `ZMod N`.
-/
theorem zmod_sum_eq_sum_Ico_one
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (F : ZMod N -> M) :
    (∑ k : ZMod N, F k) =
      ∑ r ∈ Finset.Ico 1 (N + 1), F (r : ZMod N) := by
  classical
  refine Finset.sum_bij'
    (s := Finset.univ) (t := Finset.Ico 1 (N + 1))
    (f := F) (g := fun r : Nat => F (r : ZMod N))
    (fun a _ => if a = 0 then N else a.val)
    (fun r _ => (r : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro a _ha
    by_cases ha0 : a = 0
    · rw [if_pos ha0]
      exact Finset.mem_Ico.mpr
        ⟨Nat.succ_le_iff.mpr (NeZero.pos N), Nat.lt_succ_self N⟩
    · have hpos : 0 < a.val := (ZMod.val_pos).mpr ha0
      have hlt : a.val < N := ZMod.val_lt a
      rw [if_neg ha0]
      exact Finset.mem_Ico.mpr
        ⟨Nat.succ_le_iff.mpr hpos, Nat.lt_succ_of_lt hlt⟩
  · intro r _hr
    simp
  · intro a _ha
    by_cases ha0 : a = 0
    · rw [if_pos ha0, ha0]
      simp
    · rw [if_neg ha0]
      exact ZMod.natCast_zmod_val a
  · intro r hr
    by_cases hrN : r = N
    · simp [hrN]
    · have hr_bounds := Finset.mem_Ico.mp hr
      have hr_le_N : r ≤ N := Nat.lt_succ_iff.mp hr_bounds.2
      have hr_lt_N : r < N := Nat.lt_of_le_of_ne hr_le_N hrN
      have hne : (r : ZMod N) ≠ 0 := by
        intro hz
        have hval_zero : (r : ZMod N).val = 0 :=
          (ZMod.val_eq_zero (r : ZMod N)).mpr hz
        have hval_r : (r : ZMod N).val = r :=
          ZMod.val_natCast_of_lt hr_lt_N
        have hr_pos : 0 < r := Nat.succ_le_iff.mp hr_bounds.1
        omega
      simp [hne, ZMod.val_natCast_of_lt hr_lt_N]
  · intro a _ha
    by_cases ha0 : a = 0
    · rw [if_pos ha0, ha0]
      simp
    · rw [if_neg ha0, ZMod.natCast_zmod_val]

/--
Each full period block can be written in regularized form by subtracting the
period endpoint power inside the block.

The subtracted constant contributes zero because the additive-character
coefficients have zero mean on the block.  This is the finite algebraic step
that exposes the `O(m^(-x-1))` decay mechanism needed for the Hurwitz/
`ZMod.LFunction` comparison.
-/
theorem zmodAdditiveCharacterLSeriesPeriodBlock_eq_regularized
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    (x : Real) (m : Nat) :
    zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m =
      ∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
        ZMod.stdAddChar (j * (k : ZMod N)) *
          ((k : Complex) ^ (-(x : Complex)) -
            (((m + 1) * N : Nat) : Complex) ^ (-(x : Complex))) := by
  let endpoint : Complex :=
    (((m + 1) * N : Nat) : Complex) ^ (-(x : Complex))
  have hcoeff_zero :=
    zmodAdditiveCharacterCoeff_periodBlock_sum_eq_zero
      (N := N) (j := j) hj m
  have hconst :
      (∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
        ZMod.stdAddChar (j * (k : ZMod N)) * endpoint) = 0 := by
    rw [← Finset.sum_mul, hcoeff_zero, zero_mul]
  rw [zmodAdditiveCharacterLSeriesPeriodBlock]
  calc
    (∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
      LSeries.term
        (fun n : Nat => ZMod.stdAddChar (j * (n : ZMod N)))
        (x : Complex) k) =
        ∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
          ZMod.stdAddChar (j * (k : ZMod N)) *
            (k : Complex) ^ (-(x : Complex)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk_ne : k ≠ 0 := by
            have hk_pos : 0 < k :=
              (Nat.succ_pos (m * N)).trans_le (Finset.mem_Ico.mp hk).1
            exact ne_of_gt hk_pos
          rw [LSeries.term_of_ne_zero hk_ne, div_eq_mul_inv,
            ← Complex.cpow_neg]
    _ =
        (∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
          ZMod.stdAddChar (j * (k : ZMod N)) *
            (k : Complex) ^ (-(x : Complex))) -
        (∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
          ZMod.stdAddChar (j * (k : ZMod N)) * endpoint) := by
          rw [hconst, sub_zero]
    _ =
        ∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
          ZMod.stdAddChar (j * (k : ZMod N)) *
            ((k : Complex) ^ (-(x : Complex)) - endpoint) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro k _
          ring
    _ =
        ∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
          ZMod.stdAddChar (j * (k : ZMod N)) *
            ((k : Complex) ^ (-(x : Complex)) -
              (((m + 1) * N : Nat) : Complex) ^ (-(x : Complex))) := by
          simp [endpoint]

/--
Residue-indexed form of the regularized period block.

This is the same finite block as
`zmodAdditiveCharacterLSeriesPeriodBlock_eq_regularized`, reindexed by the
residue `r = 1, ..., N`.  It is the Hurwitz-facing normalization: the
additive-character coefficient depends only on `r`, while the power term is
`m * N + r`.
-/
theorem zmodAdditiveCharacterLSeriesPeriodBlock_eq_regularized_residueIco
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    (x : Real) (m : Nat) :
    zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m =
      ∑ r ∈ Finset.Ico 1 (N + 1),
        ZMod.stdAddChar (j * (r : ZMod N)) *
          ((((m * N + r : Nat) : Complex) ^ (-(x : Complex))) -
            (((m + 1) * N : Nat) : Complex) ^ (-(x : Complex))) := by
  rw [zmodAdditiveCharacterLSeriesPeriodBlock_eq_regularized
    (N := N) (j := j) hj x m]
  have hmap :
      (Finset.Ico 1 (N + 1)).map (addRightEmbedding (m * N)) =
        Finset.Ico (m * N + 1) ((m + 1) * N + 1) := by
    rw [Finset.map_add_right_Ico]
    congr 1 <;> ring
  rw [← hmap, Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hcast :
      (((r + m * N : Nat) : ZMod N) = (r : ZMod N)) := by
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
  simp [hcast, Nat.add_comm]

/--
Positive real scaling of a period-block power.

This is the elementary normalization behind the Hurwitz comparison:
`m * N + r = N * (m + r / N)`, so on the positive real branch the complex
power factors as `N^s * (m + r/N)^s`.
-/
theorem zmodAdditiveCharacter_periodBlock_power_factor
    {N : Nat} [NeZero N] (x : Real) (m r : Nat) :
    (((m * N + r : Nat) : Complex) ^ (-(x : Complex))) =
      ((N : Complex) ^ (-(x : Complex))) *
        (((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
          (-(x : Complex)) := by
  have hN_nonneg : 0 ≤ (N : Real) := by positivity
  have hshift_nonneg :
      0 ≤ (m : Real) + (r : Real) / (N : Real) := by positivity
  have hN_ne : (N : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  have hreal :
      ((m * N + r : Nat) : Real) =
        (N : Real) * ((m : Real) + (r : Real) / (N : Real)) := by
    rw [Nat.cast_add, Nat.cast_mul]
    field_simp [hN_ne]
  have hmul :
      ((m * N + r : Nat) : Complex) =
        ((N : Real) : Complex) *
          (((m : Real) + (r : Real) / (N : Real) : Real) : Complex) := by
    rw [← Complex.ofReal_natCast, hreal, Complex.ofReal_mul]
  rw [hmul, Complex.mul_cpow_ofReal_nonneg hN_nonneg hshift_nonneg]
  simp [Complex.ofReal_natCast]

/--
Endpoint version of `zmodAdditiveCharacter_periodBlock_power_factor`.
-/
theorem zmodAdditiveCharacter_periodBlock_endpoint_power_factor
    {N : Nat} [NeZero N] (x : Real) (m : Nat) :
    ((((m + 1) * N : Nat) : Complex) ^ (-(x : Complex))) =
      ((N : Complex) ^ (-(x : Complex))) *
        (((m + 1 : Nat) : Complex) ^ (-(x : Complex))) := by
  simpa [Nat.add_zero] using
    zmodAdditiveCharacter_periodBlock_power_factor
      (N := N) x (m + 1) 0

/--
Mean-value bound for the positive-real branch of the negative complex power.

For `0 < a <= b`, the derivative of `t ^ (-x)` has norm
`x * t ^ (-x - 1)`, hence the finite difference is controlled by the left
endpoint.  This is the analytic estimate behind the summability of the
regularized Hurwitz-shaped period blocks.
-/
theorem norm_ofReal_cpow_neg_sub_le
    {x a b : Real} (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) :
    ‖(b : Complex) ^ (-(x : Complex)) -
        (a : Complex) ^ (-(x : Complex))‖ ≤
      x * a ^ (-x - 1) * ‖b - a‖ := by
  let f : Real → Complex := fun t => (t : Complex) ^ (-(x : Complex))
  have hx_ne : (-(x : Complex)) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast (ne_of_gt hx))
  have hf : ∀ t ∈ Set.Icc a b, DifferentiableAt Real f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      ((ha.trans_le ht.1).ne') hx_ne
  have hbound :
      ∀ t ∈ Set.Icc a b, ‖deriv f t‖ ≤ x * a ^ (-x - 1) := by
    intro t ht
    have ht_pos : 0 < t := ha.trans_le ht.1
    rw [Complex.deriv_ofReal_cpow_const ht_pos.ne' hx_ne]
    have hpow_norm :
        ‖(t : Complex) ^ (-(x : Complex) - 1)‖ =
          t ^ (-x - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
      simp
    have hneg_norm : ‖-(x : Complex)‖ = x := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    calc
      ‖-(x : Complex) * (t : Complex) ^ (-(x : Complex) - 1)‖ =
          x * t ^ (-x - 1) := by
            rw [norm_mul, hneg_norm, hpow_norm]
      _ ≤ x * a ^ (-x - 1) := by
            have hmono : t ^ (-x - 1) ≤ a ^ (-x - 1) :=
              (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
                (show -x - 1 ≤ 0 by linarith)) ha ht_pos ht.1
            exact mul_le_mul_of_nonneg_left hmono hx.le
  have hmean :=
    (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (f := f) hf hbound
      ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  simpa [f, mul_assoc] using hmean

/--
Residue-specialized power-difference bound for one Hurwitz-shaped block term.

For `r = 1, ..., N`, the shift `r / N` lies in `(0, 1]`, so the distance from
`m + r/N` to `m + 1` is at most one.  The mean-value estimate therefore gives
the summable majorant `x * (m + r/N)^(-x-1)`.
-/
theorem zmodAdditiveCharacter_scaledResiduePowerDiff_norm_le
    {N : Nat} [NeZero N] {x : Real} (hx : 0 < x)
    {r : Nat} (hr : r ∈ Finset.Ico 1 (N + 1)) (m : Nat) :
    ‖(((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
          (-(x : Complex)) -
        (((m + 1 : Nat) : Complex) ^ (-(x : Complex)))‖ ≤
      x * ((m : Real) + (r : Real) / (N : Real)) ^ (-x - 1) := by
  have hN_pos_nat : 0 < N := NeZero.pos N
  have hN_pos : 0 < (N : Real) := by exact_mod_cast hN_pos_nat
  have hr_bounds := Finset.mem_Ico.mp hr
  have hr_pos_nat : 0 < r := Nat.succ_le_iff.mp hr_bounds.1
  have hr_pos : 0 < (r : Real) := by exact_mod_cast hr_pos_nat
  have hr_le_N_nat : r ≤ N := Nat.lt_succ_iff.mp hr_bounds.2
  have hr_le_N : (r : Real) ≤ (N : Real) := by exact_mod_cast hr_le_N_nat
  have hfrac_pos : 0 < (r : Real) / (N : Real) :=
    div_pos hr_pos hN_pos
  have hfrac_le_one : (r : Real) / (N : Real) ≤ 1 := by
    rw [div_le_one hN_pos]
    exact hr_le_N
  let a : Real := (m : Real) + (r : Real) / (N : Real)
  let b : Real := (m + 1 : Nat)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) hfrac_pos
  have hab : a ≤ b := by
    dsimp [a, b]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hdist_le_one : ‖b - a‖ ≤ (1 : Real) := by
    have hnonneg : 0 ≤ b - a := sub_nonneg.mpr hab
    have hle : b - a ≤ 1 := by
      dsimp [a, b]
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hmean := norm_ofReal_cpow_neg_sub_le hx ha_pos hab
  calc
    ‖(((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
          (-(x : Complex)) -
        (((m + 1 : Nat) : Complex) ^ (-(x : Complex)))‖ =
        ‖(b : Complex) ^ (-(x : Complex)) -
          (a : Complex) ^ (-(x : Complex))‖ := by
          simp [a, b, norm_sub_rev]
    _ ≤ x * a ^ (-x - 1) * ‖b - a‖ := hmean
    _ ≤ x * a ^ (-x - 1) * 1 := by
          exact mul_le_mul_of_nonneg_left hdist_le_one
            (mul_nonneg hx.le (Real.rpow_nonneg ha_pos.le _))
    _ = x * ((m : Real) + (r : Real) / (N : Real)) ^ (-x - 1) := by
          simp [a]

/--
The residue-level mean-value majorant is summable.

This is the analytic payoff of gaining one power from the zero-mean
regularization: `x * (m + r/N)^(-x-1)` is a shifted p-series with exponent
`x + 1 > 1`.
-/
theorem summable_zmodAdditiveCharacter_scaledResiduePowerDiff_majorant
    {N : Nat} [NeZero N] {x : Real} (hx : 0 < x)
    {r : Nat} (hr : r ∈ Finset.Ico 1 (N + 1)) :
    Summable fun m : Nat =>
      x * ((m : Real) + (r : Real) / (N : Real)) ^ (-x - 1) := by
  have hN_pos_nat : 0 < N := NeZero.pos N
  have hN_pos : 0 < (N : Real) := by exact_mod_cast hN_pos_nat
  have hr_pos_nat : 0 < r :=
    Nat.succ_le_iff.mp (Finset.mem_Ico.mp hr).1
  have hr_pos : 0 < (r : Real) := by exact_mod_cast hr_pos_nat
  have hfrac_pos : 0 < (r : Real) / (N : Real) :=
    div_pos hr_pos hN_pos
  have hshift :
      Summable fun m : Nat =>
        1 / |(m : Real) + (r : Real) / (N : Real)| ^ (x + 1) :=
    (Real.summable_one_div_nat_add_rpow
      ((r : Real) / (N : Real)) (x + 1)).mpr (by linarith)
  have hcore :
      Summable fun m : Nat =>
        ((m : Real) + (r : Real) / (N : Real)) ^ (-x - 1) := by
    refine hshift.congr ?_
    intro m
    have hbase_pos :
        0 < (m : Real) + (r : Real) / (N : Real) :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) hfrac_pos
    rw [abs_of_pos hbase_pos, show -x - 1 = -(x + 1) by ring,
      Real.rpow_neg hbase_pos.le]
    simp [one_div]
  exact Summable.mul_left x hcore

/--
For each residue in a complete period, the Hurwitz-shaped finite-difference
terms are norm-summable in the block index.
-/
theorem summable_zmodAdditiveCharacter_scaledResiduePowerDiff_norm
    {N : Nat} [NeZero N] {x : Real} (hx : 0 < x)
    {r : Nat} (hr : r ∈ Finset.Ico 1 (N + 1)) :
    Summable fun m : Nat =>
      ‖(((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
          (-(x : Complex)) -
        (((m + 1 : Nat) : Complex) ^ (-(x : Complex)))‖ := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) ?_
    (summable_zmodAdditiveCharacter_scaledResiduePowerDiff_majorant
      (N := N) hx hr)
  intro m
  exact zmodAdditiveCharacter_scaledResiduePowerDiff_norm_le
    (N := N) hx hr m

/--
For each residue in a complete period, the Hurwitz-shaped finite-difference
terms are summable as complex terms.
-/
theorem summable_zmodAdditiveCharacter_scaledResiduePowerDiff
    {N : Nat} [NeZero N] {x : Real} (hx : 0 < x)
    {r : Nat} (hr : r ∈ Finset.Ico 1 (N + 1)) :
    Summable fun m : Nat =>
      (((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
          (-(x : Complex)) -
        (((m + 1 : Nat) : Complex) ^ (-(x : Complex))) := by
  rw [← summable_norm_iff]
  exact summable_zmodAdditiveCharacter_scaledResiduePowerDiff_norm
    (N := N) hx hr

/--
Hurwitz-scaled residue form of the regularized period block.

All dependence on the modulus scale is now carried by the common factor
`N^(-x)`, and the remaining finite sum has the Hurwitz-shifted powers
`(m + r/N)^(-x)` and `(m + 1)^(-x)`.
-/
theorem zmodAdditiveCharacterLSeriesPeriodBlock_eq_scaled_residueIco
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    (x : Real) (m : Nat) :
    zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m =
      ((N : Complex) ^ (-(x : Complex))) *
        ∑ r ∈ Finset.Ico 1 (N + 1),
          ZMod.stdAddChar (j * (r : ZMod N)) *
            ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
                (-(x : Complex)) -
              (((m + 1 : Nat) : Complex) ^ (-(x : Complex)))) := by
  rw [zmodAdditiveCharacterLSeriesPeriodBlock_eq_regularized_residueIco
    (N := N) (j := j) hj x m]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [zmodAdditiveCharacter_periodBlock_power_factor (N := N) x m r,
    zmodAdditiveCharacter_periodBlock_endpoint_power_factor (N := N) x m]
  ring

/--
The complete-period block series is summable for every `x > 0`.

This is the checked block-level Dirichlet continuation estimate: after
zero-mean regularization, each residue contributes a shifted p-series
majorant of exponent `x + 1`, and the complete block is only a finite residue
sum times the harmless scale `N^(-x)`.
-/
theorem summable_zmodAdditiveCharacterLSeriesPeriodBlock_of_pos
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    Summable fun m : Nat =>
      zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m := by
  have hresidue_sum :
      Summable fun m : Nat =>
        ∑ r ∈ Finset.Ico 1 (N + 1),
          ZMod.stdAddChar (j * (r : ZMod N)) *
            ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
                (-(x : Complex)) -
              (((m + 1 : Nat) : Complex) ^ (-(x : Complex)))) := by
    refine summable_sum (s := Finset.Ico 1 (N + 1)) ?_
    intro r hr
    exact Summable.mul_left (ZMod.stdAddChar (j * (r : ZMod N)))
      (summable_zmodAdditiveCharacter_scaledResiduePowerDiff
        (N := N) hx hr)
  have hscaled :
      Summable fun m : Nat =>
        ((N : Complex) ^ (-(x : Complex))) *
          ∑ r ∈ Finset.Ico 1 (N + 1),
            ZMod.stdAddChar (j * (r : ZMod N)) *
              ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
                  (-(x : Complex)) -
                (((m + 1 : Nat) : Complex) ^ (-(x : Complex)))) :=
    Summable.mul_left ((N : Complex) ^ (-(x : Complex))) hresidue_sum
  exact hscaled.congr fun m =>
    (zmodAdditiveCharacterLSeriesPeriodBlock_eq_scaled_residueIco
      (N := N) (j := j) hj x m).symm

/--
Norm-control reduction for the regularized period block.

The additive-character coefficient has norm `1`, so absolute convergence of
the period-block series is reduced to bounding only the finite power
differences inside each period.
-/
theorem zmodAdditiveCharacterLSeriesPeriodBlock_norm_le_powerDiffSum
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    (x : Real) (m : Nat) :
    ‖zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m‖ ≤
      ∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
        ‖(k : Complex) ^ (-(x : Complex)) -
          (((m + 1) * N : Nat) : Complex) ^ (-(x : Complex))‖ := by
  rw [zmodAdditiveCharacterLSeriesPeriodBlock_eq_regularized
    (N := N) (j := j) hj x m]
  calc
    ‖(∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
        ZMod.stdAddChar (j * (k : ZMod N)) *
          ((k : Complex) ^ (-(x : Complex)) -
            (((m + 1) * N : Nat) : Complex) ^ (-(x : Complex))))‖ ≤
        ∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
          ‖ZMod.stdAddChar (j * (k : ZMod N)) *
            ((k : Complex) ^ (-(x : Complex)) -
              (((m + 1) * N : Nat) : Complex) ^ (-(x : Complex)))‖ :=
      norm_sum_le _ _
    _ =
        ∑ k ∈ Finset.Ico (m * N + 1) ((m + 1) * N + 1),
          ‖(k : Complex) ^ (-(x : Complex)) -
            (((m + 1) * N : Nat) : Complex) ^ (-(x : Complex))‖ := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [norm_mul]
      simp

/--
The checked additive-character boundary value is the limit of complete
period-block partial sums.

The remaining `ZMod.LFunction` comparison can now be attacked block-by-block,
where the nontrivial additive character has exact zero mean on every period.
-/
theorem zmodAdditiveCharacterBoundaryValue_tendsto_periodBlockPartialSums
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    Tendsto
      (fun M : Nat =>
        ∑ m ∈ Finset.range M,
          zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m)
      atTop
      (nhds (zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx)) := by
  have hcond :=
    zmodAdditiveCharacterBoundaryValue_hasSum_conditional_lseriesTerm
      (N := N) (j := j) hj (x := x) hx
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff] at hcond
  have hcut : Tendsto (fun M : Nat => M * N + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    refine eventually_atTop.2 ⟨b, ?_⟩
    intro M hM
    have hN : 0 < N := NeZero.pos N
    have hMle : M ≤ M * N + 1 := by
      nlinarith
    exact hM.trans hMle
  refine (hcond.comp hcut).congr (fun M => ?_)
  exact (zmodAdditiveCharacterLSeriesPeriodBlock_partial_sum_eq_range
    (N := N) j x M).symm

/--
The summable complete-period block series has the checked boundary value as
its ordinary infinite sum.

This packages the new absolute/summable block estimate with the previously
checked conditional-boundary limit.
-/
theorem zmodAdditiveCharacterLSeriesPeriodBlock_hasSum_boundaryValue
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    HasSum
      (fun m : Nat =>
        zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m)
      (zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx) := by
  exact
    (Summable.hasSum_iff_tendsto_nat
      (summable_zmodAdditiveCharacterLSeriesPeriodBlock_of_pos
        (N := N) (j := j) hj hx)).mpr
      (zmodAdditiveCharacterBoundaryValue_tendsto_periodBlockPartialSums
        (N := N) (j := j) hj hx)

/--
Tsum form of the complete-period block representation of the checked boundary
value.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_tsum_periodBlock
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
      ∑' m : Nat, zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m := by
  exact
    (zmodAdditiveCharacterLSeriesPeriodBlock_hasSum_boundaryValue
      (N := N) (j := j) hj hx).tsum_eq.symm

/--
Hurwitz-difference tail form of the checked additive-character boundary value.

This is the exact summable normal form behind the remaining continuation
problem: each complete period block has been converted into a finite sum of
absolutely summable tails
`(m + r/N)^(-x) - (m + 1)^(-x)`.  The only analytic identity still missing
from this shape is the comparison of each regularized tail with the
corresponding difference of Hurwitz-zeta branches.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_scaled_residueDiff_tsum
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
      ((N : Complex) ^ (-(x : Complex))) *
        ∑ r ∈ Finset.Ico 1 (N + 1),
          ZMod.stdAddChar (j * (r : ZMod N)) *
            (∑' m : Nat,
              ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
                  (-(x : Complex)) -
                (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) := by
  rw [zmodAdditiveCharacterBoundaryValue_eq_tsum_periodBlock
    (N := N) (j := j) hj hx]
  have hblock :
      (∑' m : Nat,
        zmodAdditiveCharacterLSeriesPeriodBlock (N := N) j x m) =
        ∑' m : Nat,
          ((N : Complex) ^ (-(x : Complex))) *
            ∑ r ∈ Finset.Ico 1 (N + 1),
              ZMod.stdAddChar (j * (r : ZMod N)) *
                ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
                    (-(x : Complex)) -
                  (((m + 1 : Nat) : Complex) ^ (-(x : Complex)))) := by
    exact tsum_congr fun m =>
      zmodAdditiveCharacterLSeriesPeriodBlock_eq_scaled_residueIco
        (N := N) (j := j) hj x m
  rw [hblock, tsum_mul_left]
  rw [Summable.tsum_finsetSum
    (f := fun r : Nat => fun m : Nat =>
      ZMod.stdAddChar (j * (r : ZMod N)) *
        ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
            (-(x : Complex)) -
          (((m + 1 : Nat) : Complex) ^ (-(x : Complex)))))
    (s := Finset.Ico 1 (N + 1))]
  · refine congrArg (fun z : Complex =>
      ((N : Complex) ^ (-(x : Complex))) * z) ?_
    refine Finset.sum_congr rfl ?_
    intro r _hr
    rw [tsum_mul_left]
  · intro r hr
    exact Summable.mul_left (ZMod.stdAddChar (j * (r : ZMod N)))
      (summable_zmodAdditiveCharacter_scaledResiduePowerDiff
        (N := N) hx hr)

/--
Conditional Hurwitz-branch form of the boundary value.

If the regularized tail
`sum_m ((m + r/N)^(-x) - (m + 1)^(-x))` is identified with the corresponding
Hurwitz-zeta branch difference, the finite zero mean of the additive character
cancels the common `a = 1` branch and leaves exactly the finite
Hurwitz-facing residue sum.  This isolates the next hard analytic lemma.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_scaled_hurwitzIco_of_regularizedTail
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x)
    (htail : ∀ r : Nat, r ∈ Finset.Ico 1 (N + 1) ->
      (∑' m : Nat,
        ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
            (-(x : Complex)) -
          (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) =
        HurwitzZeta.hurwitzZeta
            (((r : Real) / (N : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex)) :
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
      ((N : Complex) ^ (-(x : Complex))) *
        ∑ r ∈ Finset.Ico 1 (N + 1),
          ZMod.stdAddChar (j * (r : ZMod N)) *
            HurwitzZeta.hurwitzZeta
              (((r : Real) / (N : Real) : Real) : UnitAddCircle)
              (x : Complex) := by
  rw [zmodAdditiveCharacterBoundaryValue_eq_scaled_residueDiff_tsum
    (N := N) (j := j) hj hx]
  congr 1
  calc
    (∑ r ∈ Finset.Ico 1 (N + 1),
      ZMod.stdAddChar (j * (r : ZMod N)) *
        (∑' m : Nat,
          ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
              (-(x : Complex)) -
            (((m + 1 : Nat) : Complex) ^ (-(x : Complex)))))) =
        ∑ r ∈ Finset.Ico 1 (N + 1),
          ZMod.stdAddChar (j * (r : ZMod N)) *
            (HurwitzZeta.hurwitzZeta
                (((r : Real) / (N : Real) : Real) : UnitAddCircle)
                (x : Complex) -
              HurwitzZeta.hurwitzZeta
                ((1 : Real) : UnitAddCircle) (x : Complex)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [htail r hr]
    _ =
        ∑ r ∈ Finset.Ico 1 (N + 1),
          (ZMod.stdAddChar (j * (r : ZMod N)) *
              HurwitzZeta.hurwitzZeta
                (((r : Real) / (N : Real) : Real) : UnitAddCircle)
                (x : Complex) -
            ZMod.stdAddChar (j * (r : ZMod N)) *
              HurwitzZeta.hurwitzZeta
                ((1 : Real) : UnitAddCircle) (x : Complex)) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          ring
    _ =
        (∑ r ∈ Finset.Ico 1 (N + 1),
          ZMod.stdAddChar (j * (r : ZMod N)) *
            HurwitzZeta.hurwitzZeta
              (((r : Real) / (N : Real) : Real) : UnitAddCircle)
              (x : Complex)) -
          ∑ r ∈ Finset.Ico 1 (N + 1),
            ZMod.stdAddChar (j * (r : ZMod N)) *
              HurwitzZeta.hurwitzZeta
                ((1 : Real) : UnitAddCircle) (x : Complex) := by
          rw [Finset.sum_sub_distrib]
    _ =
        ∑ r ∈ Finset.Ico 1 (N + 1),
          ZMod.stdAddChar (j * (r : ZMod N)) *
            HurwitzZeta.hurwitzZeta
              (((r : Real) / (N : Real) : Real) : UnitAddCircle)
              (x : Complex) := by
          have hpole :
              (∑ r ∈ Finset.Ico 1 (N + 1),
                ZMod.stdAddChar (j * (r : ZMod N)) *
                  HurwitzZeta.hurwitzZeta
                    ((1 : Real) : UnitAddCircle) (x : Complex)) = 0 := by
            rw [← Finset.sum_mul]
            rw [zmodAdditiveCharacterCoeff_Ico_one_period_sum_eq_zero
              (N := N) (j := j) hj, zero_mul]
          rw [hpole, sub_zero]

/--
Mathlib's `ZMod.LFunction` written in the same `Ico 1 (N + 1)` residue
coordinates as the regularized block route.

The endpoint residue `r = N` represents `0 : ZMod N`; its Hurwitz parameter is
`1`, which is the same point of `UnitAddCircle` as `0`.
-/
theorem zmodAdditiveCharacterLFunction_eq_scaled_hurwitzIco
    {N : Nat} [NeZero N] (j : ZMod N) (s : Complex) :
    ZMod.LFunction
        (fun k : ZMod N => ZMod.stdAddChar (j * k)) s =
      ((N : Complex) ^ (-s)) *
        ∑ r ∈ Finset.Ico 1 (N + 1),
          ZMod.stdAddChar (j * (r : ZMod N)) *
            HurwitzZeta.hurwitzZeta
              (((r : Real) / (N : Real) : Real) : UnitAddCircle) s := by
  rw [ZMod.LFunction]
  congr 1
  rw [zmod_sum_eq_sum_Ico_one
    (N := N)
    (F := fun k : ZMod N =>
      ZMod.stdAddChar (j * k) *
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s)]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [ZMod.toAddCircle_natCast]

/--
The regularized Hurwitz-tail identity is now the only analytic input needed to
obtain the Mathlib `ZMod.LFunction` value from the checked boundary value.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_lFunction_of_regularizedTail
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x)
    (htail : ∀ r : Nat, r ∈ Finset.Ico 1 (N + 1) ->
      (∑' m : Nat,
        ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
            (-(x : Complex)) -
          (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) =
        HurwitzZeta.hurwitzZeta
            (((r : Real) / (N : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex)) :
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
      ZMod.LFunction
        (fun k : ZMod N => ZMod.stdAddChar (j * k))
        (x : Complex) := by
  calc
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
        ((N : Complex) ^ (-(x : Complex))) *
          ∑ r ∈ Finset.Ico 1 (N + 1),
            ZMod.stdAddChar (j * (r : ZMod N)) *
              HurwitzZeta.hurwitzZeta
                (((r : Real) / (N : Real) : Real) : UnitAddCircle)
                (x : Complex) :=
      zmodAdditiveCharacterBoundaryValue_eq_scaled_hurwitzIco_of_regularizedTail
        (N := N) (j := j) hj hx htail
    _ = ZMod.LFunction
          (fun k : ZMod N => ZMod.stdAddChar (j * k))
          (x : Complex) := by
      rw [zmodAdditiveCharacterLFunction_eq_scaled_hurwitzIco
        (N := N) j (x : Complex)]

/--
The endpoint residue in the regularized Hurwitz-tail formula is automatic.

When `r = N`, the Hurwitz parameter is `1` and every regularized summand is
zero.  The hard continuation input is therefore only needed for the nonendpoint
residues `1 <= r < N`.
-/
theorem regularizedHurwitzTail_eq_hurwitzZeta_sub_of_endpoint
    {N : Nat} [NeZero N] (x : Real) :
    (∑' m : Nat,
      ((((m : Real) + (N : Real) / (N : Real) : Real) : Complex) ^
          (-(x : Complex)) -
        (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) =
      HurwitzZeta.hurwitzZeta
          (((N : Real) / (N : Real) : Real) : UnitAddCircle)
          (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex) := by
  have hN_pos : 0 < (N : Real) := by
    exact_mod_cast (NeZero.pos N)
  have hdiv : (N : Real) / (N : Real) = (1 : Real) :=
    div_self (ne_of_gt hN_pos)
  have hterms :
      (fun m : Nat =>
        ((((m : Real) + (N : Real) / (N : Real) : Real) : Complex) ^
            (-(x : Complex)) -
          (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) =
        fun _ : Nat => (0 : Complex) := by
    funext m
    have harg :
        (((m : Real) + (N : Real) / (N : Real) : Real) : Complex) =
          ((m + 1 : Nat) : Complex) := by
      simp [Nat.cast_add]
    rw [harg, sub_self]
  have htail_zero :
      (∑' m : Nat,
        ((((m : Real) + (N : Real) / (N : Real) : Real) : Complex) ^
            (-(x : Complex)) -
          (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) = 0 := by
    rw [hterms]
    simp
  rw [htail_zero, hdiv]
  simp

/--
The regularized-tail bridge only needs the nonendpoint residue identities.

The endpoint residue `r = N` is supplied by
`regularizedHurwitzTail_eq_hurwitzZeta_sub_of_endpoint`; callers only have to
prove the Hurwitz-tail continuation for `r ∈ Ico 1 N`.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_lFunction_of_regularizedTail_nonendpoint
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x)
    (htail : ∀ r : Nat, r ∈ Finset.Ico 1 N ->
      (∑' m : Nat,
        ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
            (-(x : Complex)) -
          (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) =
        HurwitzZeta.hurwitzZeta
            (((r : Real) / (N : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex)) :
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
      ZMod.LFunction
        (fun k : ZMod N => ZMod.stdAddChar (j * k))
        (x : Complex) := by
  refine
    zmodAdditiveCharacterBoundaryValue_eq_lFunction_of_regularizedTail
      (N := N) (j := j) hj hx ?_
  intro r hr
  have hr_bounds := Finset.mem_Ico.mp hr
  have hr_le_N : r ≤ N := Nat.lt_succ_iff.mp hr_bounds.2
  by_cases hrN : r = N
  · subst r
    exact regularizedHurwitzTail_eq_hurwitzZeta_sub_of_endpoint
      (N := N) x
  · have hr_lt_N : r < N := Nat.lt_of_le_of_ne hr_le_N hrN
    exact htail r (Finset.mem_Ico.mpr ⟨hr_bounds.1, hr_lt_N⟩)

/--
Abel-summation integral representation of the checked additive-character
boundary value.

This is a genuine analytic normal form for the hard conditional value: the
Dirichlet-test boundary sum is identified with an improper integral involving
the bounded additive-character partial sums.  The remaining continuation
problem can now compare this integral with Mathlib's `ZMod.LFunction`
definition.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_abelSummationIntegral
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
      (0 : Complex) -
        ∫ t in Set.Ioi (1 : Real),
          deriv (fun u : Real => (u : Complex) ^ (-(x : Complex))) t *
            (∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
              (if k = 0 then 0 else
                ZMod.stdAddChar (j * (k : ZMod N)))) := by
  let c : Nat -> Complex := fun k =>
    if k = 0 then 0 else ZMod.stdAddChar (j * (k : ZMod N))
  let f : Real -> Complex := fun u => (u : Complex) ^ (-(x : Complex))
  have hterm_eq (k : Nat) :
      f k * c k =
        LSeries.term
          (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
          (x : Complex) k := by
    by_cases hk : k = 0
    · simp [f, c, hk, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hk, div_eq_mul_inv,
        ← Complex.cpow_neg]
      simp [f, c, hk, mul_comm]
  have hboundary_Icc :
      Tendsto
        (fun n : Nat => ∑ k ∈ Finset.Icc 0 n, f k * c k)
        atTop (nhds (zmodAdditiveCharacterBoundaryValue
          (N := N) (j := j) hj (x := x) hx)) := by
    have hcond :=
      zmodAdditiveCharacterBoundaryValue_hasSum_conditional_lseriesTerm
        (N := N) (j := j) hj (x := x) hx
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff] at hcond
    have hcond_succ :=
      (tendsto_add_atTop_iff_nat
        (f := fun n : Nat =>
          (Finset.range n).sum
            (fun k : Nat =>
              LSeries.term
                (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
                (x : Complex) k))
        (l := nhds (zmodAdditiveCharacterBoundaryValue
          (N := N) (j := j) hj (x := x) hx)) 1).mpr hcond
    refine hcond_succ.congr (fun n => ?_)
    rw [Nat.range_succ_eq_Icc_zero]
    refine Finset.sum_congr rfl ?_
    intro k _
    exact (hterm_eq k).symm
  have hsum_bdd :
      IsBoundedUnder (· ≤ ·) (atTop : Filter Nat)
        ((‖·‖) ∘ fun n : Nat => ∑ k ∈ Finset.Icc 0 n, c k) := by
    rcases zmodAdditiveCharacterCoeff_Icc_zero_partialSums_bounded
        (N := N) (j := j) hj with
      ⟨B, _hB_nonneg, hB⟩
    refine ⟨B, ?_⟩
    exact (show ∀ᶠ n : Nat in atTop,
        ‖(∑ k ∈ Finset.Icc 0 n, c k)‖ ≤ B from
      Eventually.of_forall fun n => by
        simpa [c] using hB n)
  have hf_tendsto : Tendsto (fun n : Nat => f n) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hreal :
        Tendsto (fun n : Nat => (n : Real) ^ (-x)) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hx).comp tendsto_natCast_atTop_atTop
    refine hreal.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : 0 < (n : Real) := by exact_mod_cast hn
    change (n : Real) ^ (-x) =
      ‖((n : Real) : Complex) ^ (-(x : Complex))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp
  have hlim :
      Tendsto
        (fun n : Nat => f n * ∑ k ∈ Finset.Icc 0 n, c k)
        atTop (nhds (0 : Complex)) :=
    hf_tendsto.zero_mul_isBoundedUnder_le hsum_bdd
  have hx_ne : (-(x : Complex)) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast (ne_of_gt hx))
  have hf_diff :
      ∀ t ∈ Set.Ici (1 : Real), DifferentiableAt Real f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      (zero_lt_one.trans_le ht).ne' hx_ne
  have hpow_re_neg : (-(x : Complex)).re < 0 := by
    simpa using neg_lt_zero.mpr hx
  have hf_int :
      LocallyIntegrableOn (deriv f) (Set.Ici (1 : Real)) := by
    simpa [f] using
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
        (integrableOn_Ioi_deriv_ofReal_cpow
          (s := -(x : Complex)) zero_lt_one hpow_re_neg)).locallyIntegrableOn
  have hderivO :
      (deriv f) =O[atTop]
        fun t : Real => t ^ ((-(x : Complex)).re - 1) := by
    simpa [f] using
      (isBigO_deriv_ofReal_cpow_const_atTop (-(x : Complex)))
  have hsumO :
      (fun t : Real => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
        fun _ : Real => (1 : Real) := by
    simpa [c] using
      zmodAdditiveCharacterCoeff_Icc_zero_floor_partialSums_isBigO_one
        (N := N) (j := j) hj
  have hg_dom :
      (fun t : Real =>
        deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
        fun t : Real => t ^ ((-(x : Complex)).re - 1) := by
    simpa [Pi.mul_apply, mul_one] using hderivO.mul hsumO
  have hg_int :
      IntegrableAtFilter
        (fun t : Real => t ^ ((-(x : Complex)).re - 1)) atTop := by
    rw [integrableAtFilter_rpow_atTop_iff]
    simpa using (by linarith [hx] :
      (-(x : Complex)).re - 1 < (-1 : Real))
  have habel :
      Tendsto
        (fun n : Nat => ∑ k ∈ Finset.Icc 0 n, f k * c k)
        atTop
        (nhds
          ((0 : Complex) -
            ∫ t in Set.Ioi (1 : Real),
              deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)) := by
    exact
      tendsto_sum_mul_atTop_nhds_one_sub_integral₀
        (c := c) (f := f) (by simp [c]) hf_diff hf_int
        (l := (0 : Complex)) hlim hg_dom hg_int
  simpa [f, c] using tendsto_nhds_unique hboundary_Icc habel

/--
Residue-prefix Abel integral representation of the checked additive-character
boundary value.

Compared with `zmodAdditiveCharacterBoundaryValue_eq_abelSummationIntegral`,
this removes the growing floor cutoff from the integrand: the coefficient
factor is exactly the finite prefix indexed by `⌊t⌋₊ % N`.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_abelSummationResiduePrefixIntegral
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
      (0 : Complex) -
        ∫ t in Set.Ioi (1 : Real),
          deriv (fun u : Real => (u : Complex) ^ (-(x : Complex))) t *
            (∑ k ∈ Finset.Icc 0 (⌊t⌋₊ % N),
              (if k = 0 then 0 else
                ZMod.stdAddChar (j * (k : ZMod N)))) := by
  rw [zmodAdditiveCharacterBoundaryValue_eq_abelSummationIntegral
    (N := N) (j := j) hj (x := x) hx]
  simp_rw [zmodAdditiveCharacterCoeff_Icc_zero_floor_sum_eq_mod
    (N := N) (j := j) hj]

/--
Explicit-kernel form of the residue-prefix Abel integral.

On the positive integration domain the derivative is the concrete kernel
`-x * t^(-x - 1)`, leaving only the finite residue-prefix coefficient factor
as the remaining arithmetic input.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_residuePrefixKernelIntegral
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
      (0 : Complex) -
        ∫ t in Set.Ioi (1 : Real),
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (∑ k ∈ Finset.Icc 0 (⌊t⌋₊ % N),
              (if k = 0 then 0 else
                ZMod.stdAddChar (j * (k : ZMod N)))) := by
  rw [zmodAdditiveCharacterBoundaryValue_eq_abelSummationResiduePrefixIntegral
    (N := N) (j := j) hj (x := x) hx]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht_ne : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have hx_ne : (-(x : Complex)) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast (ne_of_gt hx))
  change
    deriv (fun u : Real => (u : Complex) ^ (-(x : Complex))) t *
        (∑ k ∈ Finset.Icc 0 (⌊t⌋₊ % N),
          (if k = 0 then 0 else
            ZMod.stdAddChar (j * (k : ZMod N)))) =
      (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
        (∑ k ∈ Finset.Icc 0 (⌊t⌋₊ % N),
          (if k = 0 then 0 else
            ZMod.stdAddChar (j * (k : ZMod N))))
  rw [Complex.deriv_ofReal_cpow_const ht_ne hx_ne]

/--
Right-half-plane canary for the remaining additive-character boundary theorem.

For `1 < x`, ordinary absolute convergence identifies the checked
additive-character boundary value with Mathlib's exponential zeta value.  The
hard zero-counting blocker is the analogous statement on `0 < x < 1`, where
this proof by ordinary `LSeries` convergence is no longer available.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_expZeta_of_one_lt
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 1 < x) :
    zmodAdditiveCharacterBoundaryValue
        (N := N) (j := j) hj (x := x) (lt_trans zero_lt_one hx) =
      HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex) := by
  let coeffZ : ZMod N -> Complex :=
    fun k => ZMod.stdAddChar (j * k)
  let coeffNat : Nat -> Complex := fun n => coeffZ (n : ZMod N)
  have h_lseries :
      Summable (LSeries.term coeffNat (x : Complex)) := by
    simpa [coeffNat, coeffZ, LSeriesSummable] using
      (ZMod.LSeriesSummable_of_one_lt_re coeffZ (by simpa using hx))
  have hshift_summable :
      Summable fun n : Nat =>
        LSeries.term coeffNat (x : Complex) (n + 1) := by
    change Summable
      ((fun n : Nat => LSeries.term coeffNat (x : Complex) n) ∘
        Nat.succ)
    exact h_lseries.comp_injective Nat.succ_injective
  have hboundary_hasSum :
      HasSum
        (fun n : Nat =>
          LSeries.term coeffNat (x : Complex) (n + 1))
        (zmodAdditiveCharacterBoundaryValue
          (N := N) (j := j) hj (x := x) (lt_trans zero_lt_one hx))
        (SummationFilter.conditional Nat) := by
    simpa [coeffNat, coeffZ] using
      zmodAdditiveCharacterBoundaryValue_hasSum_conditional_shifted_lseriesTerm
        (N := N) (j := j) hj (x := x) (lt_trans zero_lt_one hx)
  have hordinary_hasSum :
      HasSum
        (fun n : Nat =>
          LSeries.term coeffNat (x : Complex) (n + 1))
        (∑' n : Nat, LSeries.term coeffNat (x : Complex) (n + 1))
        (SummationFilter.conditional Nat) :=
    hshift_summable.hasSum.mono_left
      (SummationFilter.conditional Nat).le_atTop
  have hboundary_eq_tsum :
      zmodAdditiveCharacterBoundaryValue
          (N := N) (j := j) hj (x := x) (lt_trans zero_lt_one hx) =
        ∑' n : Nat, LSeries.term coeffNat (x : Complex) (n + 1) :=
    hboundary_hasSum.unique hordinary_hasSum
  have hdecomp :
      (∑' n : Nat, LSeries.term coeffNat (x : Complex) n) =
        ∑' n : Nat, LSeries.term coeffNat (x : Complex) (n + 1) := by
    rw [h_lseries.tsum_eq_zero_add]
    simp only [LSeries.term_zero, zero_add]
  have hlfunction :
      ZMod.LFunction coeffZ (x : Complex) =
        LSeries coeffNat (x : Complex) := by
    simpa [coeffNat, coeffZ] using
      (ZMod.LFunction_eq_LSeries coeffZ (by simpa using hx))
  calc
    zmodAdditiveCharacterBoundaryValue
        (N := N) (j := j) hj (x := x) (lt_trans zero_lt_one hx) =
        ∑' n : Nat, LSeries.term coeffNat (x : Complex) (n + 1) :=
      hboundary_eq_tsum
    _ = LSeries coeffNat (x : Complex) := by
      simpa [LSeries] using hdecomp.symm
    _ = ZMod.LFunction coeffZ (x : Complex) := hlfunction.symm
    _ = HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex) := by
      simpa [coeffZ] using
        (ZMod.LFunction_stdAddChar_eq_expZeta
          j (x : Complex) (Or.inl hj))

/--
Abel's theorem transports the checked boundary partial-sum limit to the
left-real radial limit of the additive-character power series.
-/
theorem zmodAdditiveCharacterAbelPowerSeries_tendsto_boundaryValue {N : Nat}
    [NeZero N] {j : ZMod N} (hj : j ≠ 0) {x : Real} (hx : 0 < x) :
    Tendsto
      (fun z : Complex =>
        ∑' n : Nat,
          zmodAdditiveCharacterAbelSeriesTerm j x n * z ^ n)
      ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
      (nhds (zmodAdditiveCharacterBoundaryValue hj hx)) :=
  Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
    (zmodAdditiveCharacterBoundaryValue_spec hj hx)

/--
The remaining value-identification theorem after Dirichlet convergence: the
checked boundary value should be the exponential-zeta continuation.
-/
def ZModAdditiveCharacterBoundaryValueExpZetaFormula : Prop :=
  forall (N : Nat) [NeZero N] (j : ZMod N),
    forall (hj : j ≠ 0),
      forall x : Real,
        forall (hx : 0 < x),
          x < 1 ->
            zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
              (x := x) hx =
              HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex)

/--
Conditional-L-series form of the remaining additive-character value theorem.

The partial sums and convergence are already checked by Dirichlet's test; the
remaining analytic input is exactly the identification of this conditional
Dirichlet-series value with Mathlib's exponential-zeta continuation.
-/
def ZModAdditiveCharacterShiftedConditionalLSeriesExpZetaFormula : Prop :=
  forall (N : Nat) [NeZero N] (j : ZMod N),
    forall (_hj : j ≠ 0),
      forall x : Real,
        forall (_hx : 0 < x),
          x < 1 ->
            (∑'[SummationFilter.conditional Nat] n : Nat,
              LSeries.term
                (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
                (x : Complex) (n + 1)) =
              HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex)

/--
Ordinary conditional-L-series form of the remaining additive-character value
theorem, stated directly with Mathlib's `LSeries.term ... n` convention.

The index-`0` term is definitionally zero, so this is equivalent to the checked
boundary-value theorem without any positive-index shift in the statement.
-/
def ZModAdditiveCharacterConditionalLSeriesExpZetaFormula : Prop :=
  forall (N : Nat) [NeZero N] (j : ZMod N),
    forall (_hj : j ≠ 0),
      forall x : Real,
        forall (_hx : 0 < x),
          x < 1 ->
            (∑'[SummationFilter.conditional Nat] n : Nat,
              LSeries.term
                (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
                (x : Complex) n) =
              HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex)

/--
Analytic-continuation form of the remaining additive-character value theorem.

Mathlib already proves
`ZMod.LFunction_stdAddChar_eq_expZeta` away from the pole.  For nonzero
additive characters, the hard remaining theorem can therefore be stated as the
identification of the checked conditional boundary value with Mathlib's
continued finite-character `LFunction`.
-/
def ZModAdditiveCharacterBoundaryValueLFunctionFormula : Prop :=
  forall (N : Nat) [NeZero N] (j : ZMod N),
    forall (hj : j ≠ 0),
      forall x : Real,
        forall (hx : 0 < x),
          x < 1 ->
            zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
              (x := x) hx =
              ZMod.LFunction
                (fun k : ZMod N => ZMod.stdAddChar (j * k))
                (x : Complex)

/--
Right-half-plane canary for the regularized Hurwitz-tail identity.

For `1 < x`, Mathlib's ordinary Hurwitz-zeta Dirichlet series is absolutely
convergent, so the checked regularized tail is exactly the difference of the
two Hurwitz branches. The blocker remains the same identity on `0 < x < 1`,
where this direct convergence proof is unavailable.
-/
theorem regularizedHurwitzTail_eq_hurwitzZeta_sub_of_one_lt
    {N : Nat} [NeZero N] {x : Real} (hx : 1 < x)
    {r : Nat} (hr : r ∈ Finset.Ico 1 (N + 1)) :
    (∑' m : Nat,
      ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
          (-(x : Complex)) -
        (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) =
      HurwitzZeta.hurwitzZeta
          (((r : Real) / (N : Real) : Real) : UnitAddCircle)
          (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex) := by
  let a : Real := (r : Real) / (N : Real)
  have hN_pos_nat : 0 < N := NeZero.pos N
  have hN_pos : 0 < (N : Real) := by exact_mod_cast hN_pos_nat
  have hr_bounds := Finset.mem_Ico.mp hr
  have hr_pos_nat : 0 < r := Nat.succ_le_iff.mp hr_bounds.1
  have hr_pos : 0 < (r : Real) := by exact_mod_cast hr_pos_nat
  have hr_le_N_nat : r ≤ N := Nat.lt_succ_iff.mp hr_bounds.2
  have hr_le_N : (r : Real) ≤ (N : Real) := by exact_mod_cast hr_le_N_nat
  have ha_pos : 0 < a := by
    dsimp [a]
    exact div_pos hr_pos hN_pos
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hN_pos]
    exact hr_le_N
  have ha_mem : a ∈ Set.Icc (0 : Real) 1 := ⟨ha_pos.le, ha_le_one⟩
  have hs : 1 < Complex.re (x : Complex) := by
    simpa using hx
  have htail_a :
      HasSum
        (fun m : Nat =>
          ((((m : Real) + a : Real) : Complex) ^ (-(x : Complex))))
        (HurwitzZeta.hurwitzZeta (a : UnitAddCircle) (x : Complex)) := by
    refine
      (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
        (a := a) ha_mem (s := (x : Complex)) hs).congr_fun ?_
    intro m
    simp [Complex.cpow_neg, one_div]
  have htail_one :
      HasSum
        (fun m : Nat =>
          (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))
        (HurwitzZeta.hurwitzZeta ((1 : Real) : UnitAddCircle)
          (x : Complex)) := by
    have hone_mem : (1 : Real) ∈ Set.Icc (0 : Real) 1 := by
      constructor <;> norm_num
    refine
      (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
        (a := (1 : Real)) hone_mem (s := (x : Complex)) hs).congr_fun ?_
    intro m
    simp [Complex.cpow_neg, one_div, Nat.cast_add]
  have hsub := htail_a.sub htail_one
  simpa [a] using hsub.tsum_eq

/--
Right-half-plane canary for the full regularized-tail route to
`ZMod.LFunction`.

This reuses the same bridge as the `0 < x < 1` target, with the new
right-half-plane tail identity filling the residue-tail input.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_lFunction_of_one_lt_via_regularizedTail
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 1 < x) :
    zmodAdditiveCharacterBoundaryValue
        (N := N) (j := j) hj (x := x) (zero_lt_one.trans hx) =
      ZMod.LFunction
        (fun k : ZMod N => ZMod.stdAddChar (j * k))
        (x : Complex) :=
  zmodAdditiveCharacterBoundaryValue_eq_lFunction_of_regularizedTail
    (N := N) (j := j) hj (zero_lt_one.trans hx)
    (fun r hr =>
      regularizedHurwitzTail_eq_hurwitzZeta_sub_of_one_lt
        (N := N) (x := x) (r := r) hx hr)

/--
Regularized Hurwitz-tail form of the remaining additive-character theorem.

This is now the isolated analytic continuation input for the scaled-block
route: each absolutely summable regularized residue tail must be identified
with the corresponding difference of Hurwitz-zeta branches.
-/
def ZModAdditiveCharacterRegularizedTailHurwitzFormula : Prop :=
  forall (N : Nat) [NeZero N],
    forall x : Real,
      forall (_hx : 0 < x),
        x < 1 ->
          forall r : Nat,
            r ∈ Finset.Ico 1 (N + 1) ->
              (∑' m : Nat,
                ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
                    (-(x : Complex)) -
                  (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) =
                HurwitzZeta.hurwitzZeta
                    (((r : Real) / (N : Real) : Real) : UnitAddCircle)
                    (x : Complex) -
                  HurwitzZeta.hurwitzZeta
                    ((1 : Real) : UnitAddCircle) (x : Complex)

/--
Nonendpoint-residue form of the regularized Hurwitz-tail target.

The endpoint residue `r = N` is checked separately by
`regularizedHurwitzTail_eq_hurwitzZeta_sub_of_endpoint`, so this is the
sharper analytic obligation left by the scaled-block route.
-/
def ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula : Prop :=
  forall (N : Nat) [NeZero N],
    forall x : Real,
      forall (_hx : 0 < x),
        x < 1 ->
          forall r : Nat,
            r ∈ Finset.Ico 1 N ->
              (∑' m : Nat,
                ((((m : Real) + (r : Real) / (N : Real) : Real) : Complex) ^
                    (-(x : Complex)) -
                  (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) =
                HurwitzZeta.hurwitzZeta
                    (((r : Real) / (N : Real) : Real) : UnitAddCircle)
                    (x : Complex) -
                  HurwitzZeta.hurwitzZeta
                    ((1 : Real) : UnitAddCircle) (x : Complex)
end

end ComplexCompactExhaustion

end RiemannHypothesisProject