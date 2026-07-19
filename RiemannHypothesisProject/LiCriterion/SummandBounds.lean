import RiemannHypothesisProject.LiCriterion.CriticalLineGeometry
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Critical-line Li summand bounds

This module contains the elementary finite critical-line Li summand positivity,
unit-circle chord estimates, inverse-square height decay, and pointwise dyadic
height-decay bounds.
-/

namespace RiemannHypothesisProject

open ComplexConjugate
/-- The real Li summand attached to one critical-line point. -/
noncomputable def criticalLineLiSummand (t : Real) (n : Nat) : Real :=
  (1 - criticalLineLiRatio t ^ n).re

/-- The critical-line Li summand is even in the height. -/
theorem criticalLineLiSummand_neg (t : Real) (n : Nat) :
    criticalLineLiSummand (-t) n = criticalLineLiSummand t n := by
  unfold criticalLineLiSummand
  rw [criticalLineLiRatio_neg_eq_conj]
  have hpow :
      ((starRingEnd ℂ) (criticalLineLiRatio t)) ^ n =
        (starRingEnd ℂ) (criticalLineLiRatio t ^ n) := by
    exact (map_pow (starRingEnd ℂ) (criticalLineLiRatio t) n).symm
  have hsub :
      1 - (starRingEnd ℂ) (criticalLineLiRatio t ^ n) =
        (starRingEnd ℂ) (1 - criticalLineLiRatio t ^ n) := by
    rw [map_sub, map_one]
  calc
    (1 - ((starRingEnd ℂ) (criticalLineLiRatio t)) ^ n).re =
        (1 - (starRingEnd ℂ) (criticalLineLiRatio t ^ n)).re := by
      rw [hpow]
    _ = ((starRingEnd ℂ) (1 - criticalLineLiRatio t ^ n)).re := by
      rw [hsub]
    _ = (1 - criticalLineLiRatio t ^ n).re := by
      simpa using (Complex.conj_re (1 - criticalLineLiRatio t ^ n))

/-- Replacing a critical-line height by its absolute value does not change the Li summand. -/
theorem criticalLineLiSummand_abs (t : Real) (n : Nat) :
    criticalLineLiSummand |t| n = criticalLineLiSummand t n := by
  rcases le_total 0 t with hnonneg | hnonpos
  · rw [abs_of_nonneg hnonneg]
  · rw [abs_of_nonpos hnonpos, criticalLineLiSummand_neg]

/-- A mirrored positive/negative critical-line pair contributes twice one height. -/
theorem criticalLineLiSummand_add_neg (t : Real) (n : Nat) :
    criticalLineLiSummand t n + criticalLineLiSummand (-t) n =
      2 * criticalLineLiSummand t n := by
  rw [criticalLineLiSummand_neg]
  ring

/-- A mirrored pair can be normalized to twice the absolute-height summand. -/
theorem criticalLineLiSummand_pair_eq_two_abs (t : Real) (n : Nat) :
    criticalLineLiSummand t n + criticalLineLiSummand (-t) n =
      2 * criticalLineLiSummand |t| n := by
  rw [criticalLineLiSummand_abs, criticalLineLiSummand_add_neg]

/-- The inverse-square critical-line height factor is even in the height. -/
theorem criticalLineHeightDecay_neg (t : Real) :
    ((-t) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ =
      (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  ring_nf

/--
Replacing a critical-line height by its absolute value does not change the
inverse-square height factor.
-/
theorem criticalLineHeightDecay_abs (t : Real) :
    (|t| ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ =
      (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  rw [sq_abs]

/--
A mirrored positive/negative critical-line pair contributes twice one
inverse-square height factor.
-/
theorem criticalLineHeightDecay_add_neg (t : Real) :
    (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ +
        ((-t) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ =
      2 * (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  rw [criticalLineHeightDecay_neg]
  ring

/-- A mirrored pair can be normalized to twice the absolute-height decay factor. -/
theorem criticalLineHeightDecay_pair_eq_two_abs (t : Real) :
    (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ +
        ((-t) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ =
      2 * (|t| ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  rw [criticalLineHeightDecay_abs, criticalLineHeightDecay_add_neg]

/--
Every individual Li summand from a critical-line point is nonnegative.

This is the finite, source-side version of the positivity mechanism in the
Li/Bombieri-Lagarias criterion: powers of a unit-circle ratio have real part at
most `1`.
-/
theorem criticalLineLiSummand_nonneg (t : Real) (n : Nat) :
    0 <= criticalLineLiSummand t n := by
  have hnorm_pow : ‖criticalLineLiRatio t ^ n‖ = 1 := by
    rw [Complex.norm_pow, criticalLineLiRatio_norm, one_pow]
  have hre_le : (criticalLineLiRatio t ^ n).re <= 1 := by
    calc
      (criticalLineLiRatio t ^ n).re <= ‖criticalLineLiRatio t ^ n‖ :=
        Complex.re_le_norm _
      _ = 1 := hnorm_pow
  exact sub_nonneg.mpr hre_le

/-- The finite critical-line Li coefficient obtained by summing over heights. -/
noncomputable def finiteCriticalLineLiCoefficient
    (heights : Finset Real) (n : Nat) : Real :=
  heights.sum (fun t : Real => criticalLineLiSummand t n)

/--
Finite critical-line zero data has nonnegative Li coefficients.

The infinite zeta theorem still needs summability, multiplicity, symmetry, and
normalization hypotheses; this theorem proves the core finite positivity
calculation without hiding those future assumptions.
-/
theorem finiteCriticalLineLiCoefficient_nonneg
    (heights : Finset Real) (n : Nat) :
    0 <= finiteCriticalLineLiCoefficient heights n := by
  classical
  unfold finiteCriticalLineLiCoefficient
  exact Finset.sum_nonneg (fun t _ht => criticalLineLiSummand_nonneg t n)

/--
On the unit circle, powers move at most linearly in the exponent.  This is the
elementary telescoping estimate behind the source-side decay bound for Li
summands.
-/
theorem norm_one_sub_pow_le_nat_mul_norm_one_sub_of_norm_one
    (z : Complex) (n : Nat) (hz : ‖z‖ = 1) :
    ‖1 - z ^ n‖ <= (n : Real) * ‖1 - z‖ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hdecomp :
          1 - z ^ (n + 1) = (1 - z ^ n) + z ^ n * (1 - z) := by
        rw [pow_succ]
        ring
      calc
        ‖1 - z ^ (n + 1)‖ =
            ‖(1 - z ^ n) + z ^ n * (1 - z)‖ := by rw [hdecomp]
        _ <= ‖1 - z ^ n‖ + ‖z ^ n * (1 - z)‖ := norm_add_le _ _
        _ <= (n : Real) * ‖1 - z‖ + 1 * ‖1 - z‖ := by
          refine add_le_add ih ?_
          rw [Complex.norm_mul, Complex.norm_pow, hz, one_pow, one_mul]
        _ = ((n + 1 : Nat) : Real) * ‖1 - z‖ := by
          norm_num [Nat.cast_add, Nat.cast_one, add_mul]

/--
For a unit complex number, the real Li summand is exactly half a squared chord
length.
-/
theorem norm_one_sub_sq_eq_two_mul_one_sub_re_of_norm_one
    (z : Complex) (hz : ‖z‖ = 1) :
    ‖1 - z‖ ^ 2 = 2 * (1 - z.re) := by
  have hzsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  calc
    ‖1 - z‖ ^ 2 = Complex.normSq (1 - z) := Complex.sq_norm _
    _ = 2 * (1 - z.re) := by
      rw [Complex.normSq_sub]
      simp [hzsq]
      ring

/-- Critical-line Li summands are half squared unit-circle chord lengths. -/
theorem criticalLineLiSummand_eq_half_norm_one_sub_pow_sq
    (t : Real) (n : Nat) :
    criticalLineLiSummand t n =
      ‖1 - criticalLineLiRatio t ^ n‖ ^ 2 / 2 := by
  have hnorm_pow : ‖criticalLineLiRatio t ^ n‖ = 1 := by
    rw [Complex.norm_pow, criticalLineLiRatio_norm, one_pow]
  unfold criticalLineLiSummand
  calc
    (1 - criticalLineLiRatio t ^ n).re =
        1 - (criticalLineLiRatio t ^ n).re := by
      simp
    _ = 2 * (1 - (criticalLineLiRatio t ^ n).re) / 2 := by
      ring
    _ = ‖1 - criticalLineLiRatio t ^ n‖ ^ 2 / 2 := by
      rw [norm_one_sub_sq_eq_two_mul_one_sub_re_of_norm_one
        (criticalLineLiRatio t ^ n) hnorm_pow]

/-- The norm square of the critical-line point is `t^2 + 1/4`. -/
theorem criticalLinePoint_norm_sq (t : Real) :
    ‖criticalLinePoint t‖ ^ 2 = t ^ 2 + (1 / 2 : Real) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [criticalLinePoint]
  ring

/-- The inverse critical-line point has squared norm `(t^2 + 1/4)^{-1}`. -/
theorem criticalLinePoint_inv_norm_sq (t : Real) :
    ‖(criticalLinePoint t)⁻¹‖ ^ 2 =
      (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  rw [norm_inv, inv_pow, criticalLinePoint_norm_sq]

/--
The source-side decay estimate for critical-line Li summands.  This is the
finite-exponent estimate needed to pair Li positivity with zero-counting:
summands are controlled by a quadratic-in-`n` multiple of the inverse square of
the critical-line height.
-/
theorem criticalLineLiSummand_le_quadratic_height_decay
    (t : Real) (n : Nat) :
    criticalLineLiSummand t n <=
      ((n : Real) ^ 2 / 2) * (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  have hnorm_pow :
      ‖1 - criticalLineLiRatio t ^ n‖ <=
        (n : Real) * ‖1 - criticalLineLiRatio t‖ :=
    norm_one_sub_pow_le_nat_mul_norm_one_sub_of_norm_one
      (criticalLineLiRatio t) n (criticalLineLiRatio_norm t)
  have hnorm_pow_sq :
      ‖1 - criticalLineLiRatio t ^ n‖ ^ 2 <=
        ((n : Real) * ‖1 - criticalLineLiRatio t‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).mpr hnorm_pow
  have hratio_step :
      ‖1 - criticalLineLiRatio t‖ = ‖(criticalLinePoint t)⁻¹‖ := by
    unfold criticalLineLiRatio
    congr 1
    ring
  calc
    criticalLineLiSummand t n =
        ‖1 - criticalLineLiRatio t ^ n‖ ^ 2 / 2 :=
      criticalLineLiSummand_eq_half_norm_one_sub_pow_sq t n
    _ <= (((n : Real) * ‖1 - criticalLineLiRatio t‖) ^ 2) / 2 := by
      exact div_le_div_of_nonneg_right hnorm_pow_sq (by norm_num)
    _ = ((n : Real) ^ 2 / 2) * (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
      rw [hratio_step]
      calc
        (((n : Real) * ‖(criticalLinePoint t)⁻¹‖) ^ 2) / 2 =
            ((n : Real) ^ 2 / 2) * ‖(criticalLinePoint t)⁻¹‖ ^ 2 := by
          ring
        _ = ((n : Real) ^ 2 / 2) *
            (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
          rw [criticalLinePoint_inv_norm_sq]

/--
Pointwise dyadic shell decay for the inverse-square critical-line height
majorant.  This is the source-side height estimate before the fixed-`n` Li
factor is introduced.
-/
theorem criticalLineHeightDecay_le_dyadic_height_decay
    (t : Real) (m : Nat)
    (hheight : (2 : Real) ^ m <= |t|) :
    (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ <=
      ((((2 : Real) ^ m) ^ 2)⁻¹) := by
  have hdyadic_pos : 0 < (2 : Real) ^ m :=
    pow_pos (by norm_num) m
  have hdyadic_sq_pos : 0 < ((2 : Real) ^ m) ^ 2 :=
    sq_pos_of_pos hdyadic_pos
  have hsq_abs : ((2 : Real) ^ m) ^ 2 <= |t| ^ 2 :=
    (sq_le_sq₀ hdyadic_pos.le (abs_nonneg t)).2 hheight
  have hsq_height : ((2 : Real) ^ m) ^ 2 <= t ^ 2 := by
    simpa [sq_abs] using hsq_abs
  have hdenom_le :
      ((2 : Real) ^ m) ^ 2 <= t ^ 2 + (1 / 2 : Real) ^ 2 :=
    hsq_height.trans (le_add_of_nonneg_right (sq_nonneg _))
  exact inv_anti₀ hdyadic_sq_pos hdenom_le

/--
Pointwise dyadic shell decay for a critical-line Li summand.  If a zero height
lies in or beyond the dyadic shell with lower edge `2^m`, the summand is bounded
by the shell's inverse-square height weight.
-/
theorem criticalLineLiSummand_le_dyadic_height_decay
    (t : Real) (n m : Nat)
    (hheight : (2 : Real) ^ m <= |t|) :
    criticalLineLiSummand t n <=
      ((n : Real) ^ 2 / 2) * ((((2 : Real) ^ m) ^ 2)⁻¹) := by
  have hdyadic_pos : 0 < (2 : Real) ^ m :=
    pow_pos (by norm_num) m
  have hdyadic_sq_pos : 0 < ((2 : Real) ^ m) ^ 2 :=
    sq_pos_of_pos hdyadic_pos
  have hsq_abs : ((2 : Real) ^ m) ^ 2 <= |t| ^ 2 :=
    (sq_le_sq₀ hdyadic_pos.le (abs_nonneg t)).2 hheight
  have hsq_height : ((2 : Real) ^ m) ^ 2 <= t ^ 2 := by
    simpa [sq_abs] using hsq_abs
  have hdenom_le :
      ((2 : Real) ^ m) ^ 2 <= t ^ 2 + (1 / 2 : Real) ^ 2 :=
    hsq_height.trans (le_add_of_nonneg_right (sq_nonneg _))
  have hinv_le :
      (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ <=
        ((((2 : Real) ^ m) ^ 2)⁻¹) :=
    inv_anti₀ hdyadic_sq_pos hdenom_le
  have hscale_nonneg : 0 <= ((n : Real) ^ 2 / 2) :=
    div_nonneg (sq_nonneg _) (by norm_num)
  exact (criticalLineLiSummand_le_quadratic_height_decay t n).trans
    (mul_le_mul_of_nonneg_left hinv_le hscale_nonneg)
end RiemannHypothesisProject
