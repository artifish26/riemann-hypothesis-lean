import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualTailExpansion
import Mathlib.Algebra.Order.Chebyshev

/-!
# Structured residual-tail coefficient bounds for M100-DF6D4

This module freezes the three scalar amplitudes multiplying the exact residual
moment vectors: the comparison transform, the explicit prime-plus-smooth
difference, and the order-zero comparison sine tail.  The bounds are stated
in the precise inverse-power form consumed by the rank-one tail theorem.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- Numerator in the unconditional `O(n⁻¹)` smooth-transform estimate. -/
def suzukiDF6D4SmoothTailCoefficient : Real :=
  2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar / Real.pi

/-- Frozen amplitude of the complete-minus-comparison transform. -/
def suzukiDF6D4DeltaTailTransformBound : Real :=
  Real.sqrt 2 * Real.log 2 + suzukiDF6D4SmoothTailCoefficient / 601

theorem suzukiDF6D4SmoothTailCoefficient_nonneg :
    0 ≤ suzukiDF6D4SmoothTailCoefficient := by
  unfold suzukiDF6D4SmoothTailCoefficient
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) suzukiDF6D4RemainderVariation_nonneg)
      suzukiProjectAStar_pos.le)
    Real.pi_pos.le

theorem suzukiDF6D4DeltaTailTransformBound_nonneg :
    0 ≤ suzukiDF6D4DeltaTailTransformBound := by
  unfold suzukiDF6D4DeltaTailTransformBound
  exact add_nonneg
    (mul_nonneg (Real.sqrt_nonneg 2) (Real.log_nonneg (by norm_num)))
    (div_nonneg suzukiDF6D4SmoothTailCoefficient_nonneg (by norm_num))

theorem suzukiDF6D4SmoothTransformDifference_abs_le_coefficient
    (mode : Nat) (hmode : 1 ≤ mode) :
    |suzukiDF6D4SmoothTransformDifference mode| ≤
      suzukiDF6D4SmoothTailCoefficient / mode := by
  simpa only [suzukiDF6D4SmoothTailCoefficient] using
    suzukiDF6D4SmoothTransformDifference_abs_le mode hmode

theorem suzukiDF6D4DeltaTransform_abs_le_frozen
    (mode : Nat) (hmode : 601 ≤ mode) :
    |suzukiDF6D4PrimeSineTransform mode +
        suzukiDF6D4SmoothTransformDifference mode| ≤
      suzukiDF6D4DeltaTailTransformBound := by
  have hmodeReal : (601 : Real) ≤ mode := by exact_mod_cast hmode
  have hsmooth :=
    suzukiDF6D4SmoothTransformDifference_abs_le_coefficient mode (by omega)
  have hsmoothFrozen :
      suzukiDF6D4SmoothTailCoefficient / (mode : Real) ≤
        suzukiDF6D4SmoothTailCoefficient / 601 := by
    exact div_le_div_of_nonneg_left
      suzukiDF6D4SmoothTailCoefficient_nonneg (by norm_num) hmodeReal
  calc
    |suzukiDF6D4PrimeSineTransform mode +
        suzukiDF6D4SmoothTransformDifference mode| ≤
        |suzukiDF6D4PrimeSineTransform mode| +
          |suzukiDF6D4SmoothTransformDifference mode| := abs_add_le _ _
    _ ≤ Real.sqrt 2 * Real.log 2 +
        suzukiDF6D4SmoothTailCoefficient / (mode : Real) :=
      add_le_add (suzukiDF6D4PrimeSineTransform_abs_le mode) hsmooth
    _ ≤ Real.sqrt 2 * Real.log 2 +
        suzukiDF6D4SmoothTailCoefficient / 601 :=
      add_le_add_right hsmoothFrozen _
    _ = suzukiDF6D4DeltaTailTransformBound := by
      rfl

/-- The order-zero comparison correction has one additional inverse power. -/
theorem suzukiDF6D4ComparisonSineTail_abs_le
    (mode : Nat) (hmode : 1 ≤ mode) :
    |suzukiDF6D4ComparisonSineTail mode| ≤
      1 / (Real.pi * mode) := by
  have h := suzukiDF6D4ComparisonSineTail_abs_le_two_div_wave mode hmode
  have hmodePos : (0 : Real) < mode := by exact_mod_cast (by omega : 0 < mode)
  convert h using 1
  unfold suzukiDF6D4ComparisonWave
  field_simp [Real.pi_ne_zero, hmodePos.ne']

/-! ## Scalar coefficient functions -/

def suzukiDF6D4TailComparisonCoefficient
    (power k : Nat) : Real :=
  (((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) * Real.pi⁻¹ *
    suzukiDF6D4ComparisonSineTransform (601 + k) /
      (((601 + k : Nat) : Real) ^ power)

def suzukiDF6D4TailDeltaCoefficient
    (power k : Nat) : Real :=
  (((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) * Real.pi⁻¹ *
    (suzukiDF6D4PrimeSineTransform (601 + k) +
      suzukiDF6D4SmoothTransformDifference (601 + k)) /
      (((601 + k : Nat) : Real) ^ power)

def suzukiDF6D4TailFixedCoefficient
    (power k : Nat) : Real :=
  -(((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) * Real.pi⁻¹ /
    (((601 + k : Nat) : Real) ^ power)

/-- Even order-zero comparison correction after the constant `-π/2` part
has been moved into the sharp main tail. -/
def suzukiDF6D4TailComparisonErrorCoefficient (k : Nat) : Real :=
  (((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) * Real.pi⁻¹ *
    suzukiDF6D4ComparisonSineTail (601 + k) /
      ((601 + k : Nat) : Real)

/-- Even order-zero smooth correction after its additional `O(n⁻¹)` decay
is exposed. -/
def suzukiDF6D4TailSmoothErrorCoefficient (k : Nat) : Real :=
  (((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) * Real.pi⁻¹ *
    suzukiDF6D4SmoothTransformDifference (601 + k) /
      ((601 + k : Nat) : Real)

theorem suzukiDF6D4TailComparisonCoefficient_abs_le
    (power k : Nat) :
    |suzukiDF6D4TailComparisonCoefficient power k| ≤
      (Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound) /
        (((601 + k : Nat) : Real) ^ power) := by
  have htransform := suzukiDF6D4ComparisonSineTransform_abs_le_frozen
    (601 + k) (by omega)
  have hdenom : 0 ≤ (((601 + k : Nat) : Real) ^ power) := by positivity
  unfold suzukiDF6D4TailComparisonCoefficient
  rw [abs_div, abs_mul, abs_mul, suzukiDF6D4TailParity_real_abs,
    one_mul, abs_inv, abs_of_pos Real.pi_pos, abs_of_nonneg hdenom]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htransform (inv_nonneg.mpr Real.pi_pos.le))
    hdenom

theorem suzukiDF6D4TailDeltaCoefficient_abs_le
    (power k : Nat) :
    |suzukiDF6D4TailDeltaCoefficient power k| ≤
      (Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound) /
        (((601 + k : Nat) : Real) ^ power) := by
  have htransform := suzukiDF6D4DeltaTransform_abs_le_frozen
    (601 + k) (by omega)
  have hdenom : 0 ≤ (((601 + k : Nat) : Real) ^ power) := by positivity
  unfold suzukiDF6D4TailDeltaCoefficient
  rw [abs_div, abs_mul, abs_mul, suzukiDF6D4TailParity_real_abs,
    one_mul, abs_inv, abs_of_pos Real.pi_pos, abs_of_nonneg hdenom]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htransform (inv_nonneg.mpr Real.pi_pos.le))
    hdenom

theorem suzukiDF6D4TailFixedCoefficient_abs_le
    (power k : Nat) :
    |suzukiDF6D4TailFixedCoefficient power k| ≤
      Real.pi⁻¹ / (((601 + k : Nat) : Real) ^ power) := by
  have hdenom : 0 ≤ (((601 + k : Nat) : Real) ^ power) := by positivity
  unfold suzukiDF6D4TailFixedCoefficient
  rw [abs_div, abs_mul, abs_neg, suzukiDF6D4TailParity_real_abs,
    one_mul, abs_inv, abs_of_pos Real.pi_pos, abs_of_nonneg hdenom]

theorem suzukiDF6D4TailComparisonErrorCoefficient_abs_le (k : Nat) :
    |suzukiDF6D4TailComparisonErrorCoefficient k| ≤
      (Real.pi⁻¹ ^ 2) /
        (((601 + k : Nat) : Real) ^ 2) := by
  let n : Nat := 601 + k
  have hnPos : (0 : Real) < n := by positivity
  have htail := suzukiDF6D4ComparisonSineTail_abs_le n (by omega)
  unfold suzukiDF6D4TailComparisonErrorCoefficient
  change
    |(((suzukiDF6D4TailParity n : Rat) : Real)) * Real.pi⁻¹ *
        suzukiDF6D4ComparisonSineTail n / (n : Real)| ≤ _
  rw [abs_div, abs_mul, abs_mul, suzukiDF6D4TailParity_real_abs,
    one_mul, abs_inv, abs_of_pos Real.pi_pos,
    abs_of_pos hnPos]
  calc
    Real.pi⁻¹ * |suzukiDF6D4ComparisonSineTail n| / (n : Real) ≤
        Real.pi⁻¹ * (1 / (Real.pi * n)) / (n : Real) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr Real.pi_pos.le))
        hnPos.le
    _ = (Real.pi⁻¹ ^ 2) / (((n : Nat) : Real) ^ 2) := by
      field_simp [Real.pi_ne_zero, hnPos.ne']

theorem suzukiDF6D4TailSmoothErrorCoefficient_abs_le (k : Nat) :
    |suzukiDF6D4TailSmoothErrorCoefficient k| ≤
      (Real.pi⁻¹ * suzukiDF6D4SmoothTailCoefficient) /
        (((601 + k : Nat) : Real) ^ 2) := by
  let n : Nat := 601 + k
  have hnPos : (0 : Real) < n := by positivity
  have hsmooth := suzukiDF6D4SmoothTransformDifference_abs_le_coefficient
    n (by omega)
  unfold suzukiDF6D4TailSmoothErrorCoefficient
  change
    |(((suzukiDF6D4TailParity n : Rat) : Real)) * Real.pi⁻¹ *
        suzukiDF6D4SmoothTransformDifference n / (n : Real)| ≤ _
  rw [abs_div, abs_mul, abs_mul, suzukiDF6D4TailParity_real_abs,
    one_mul, abs_inv, abs_of_pos Real.pi_pos,
    abs_of_pos hnPos]
  calc
    Real.pi⁻¹ * |suzukiDF6D4SmoothTransformDifference n| / (n : Real) ≤
        Real.pi⁻¹ *
            (suzukiDF6D4SmoothTailCoefficient / (n : Real)) /
          (n : Real) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsmooth (inv_nonneg.mpr Real.pi_pos.le))
        hnPos.le
    _ = (Real.pi⁻¹ * suzukiDF6D4SmoothTailCoefficient) /
        (((n : Nat) : Real) ^ 2) := by
      field_simp [hnPos.ne']

/-! ## Exact coefficient-vector decompositions -/

theorem suzukiDF6D4EvenResidualTailComponent_eq_contributions
    (order k : Nat) (i : Fin 45) :
    suzukiDF6D4EvenResidualTailComponent order (601 + k) i =
      suzukiDF6D4EvenResidualTailTransformMoment order i *
          suzukiDF6D4TailComparisonCoefficient (2 * order + 1) k +
        suzukiDF6D4EvenTailTransformMoment order
            (suzukiDF6D4EvenLowMode i) *
          suzukiDF6D4TailDeltaCoefficient (2 * order + 1) k +
        suzukiDF6D4EvenResidualTailFixedMoment order i *
          suzukiDF6D4TailFixedCoefficient (2 * order + 2) k := by
  rw [suzukiDF6D4EvenResidualTailComponent_eq_momentForm
    order (601 + k) (by omega) i]
  unfold suzukiDF6D4TailComparisonCoefficient
    suzukiDF6D4TailDeltaCoefficient
    suzukiDF6D4TailFixedCoefficient
  ring

theorem suzukiDF6D4OddResidualTailComponent_eq_contributions
    (order k : Nat) (i : Fin 44) :
    suzukiDF6D4OddResidualTailComponent order (601 + k) i =
      suzukiDF6D4OddResidualTailTransformMoment order i *
          suzukiDF6D4TailComparisonCoefficient (2 * order + 2) k +
        suzukiDF6D4OddTailTransformMoment order
            (suzukiDF6D4OddLowMode i) *
          suzukiDF6D4TailDeltaCoefficient (2 * order + 2) k +
        suzukiDF6D4OddResidualTailFixedMoment order i *
          suzukiDF6D4TailFixedCoefficient (2 * order + 1) k := by
  rw [suzukiDF6D4OddResidualTailComponent_eq_momentForm
    order (601 + k) (by omega) i]
  unfold suzukiDF6D4TailComparisonCoefficient
    suzukiDF6D4TailDeltaCoefficient
    suzukiDF6D4TailFixedCoefficient
  ring

def suzukiDF6D4EvenTailMainComparisonCoefficient (k : Nat) : Real :=
  (((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) * Real.pi⁻¹ *
    (-(Real.pi / 2)) / ((601 + k : Nat) : Real)

def suzukiDF6D4EvenTailMainPrimeCoefficient (k : Nat) : Real :=
  (((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) * Real.pi⁻¹ *
    suzukiDF6D4PrimeSineTransform (601 + k) /
      ((601 + k : Nat) : Real)

theorem suzukiDF6D4EvenResidualTailMain_eq_contributions
    (k : Nat) (i : Fin 45) :
    suzukiDF6D4EvenResidualTailMain (601 + k) i =
      suzukiDF6D4EvenResidualTailTransformMoment 0 i *
          suzukiDF6D4EvenTailMainComparisonCoefficient k +
        suzukiDF6D4EvenTailTransformMoment 0
            (suzukiDF6D4EvenLowMode i) *
          suzukiDF6D4EvenTailMainPrimeCoefficient k := by
  unfold suzukiDF6D4EvenResidualTailMain
    suzukiDF6D4EvenTailMainComparisonCoefficient
    suzukiDF6D4EvenTailMainPrimeCoefficient
  ring

theorem suzukiDF6D4EvenResidualTailOrderZeroRemainder_eq_contributions
    (k : Nat) (i : Fin 45) :
    suzukiDF6D4EvenResidualTailOrderZeroRemainder (601 + k) i =
      suzukiDF6D4EvenResidualTailTransformMoment 0 i *
          suzukiDF6D4TailComparisonErrorCoefficient k +
        suzukiDF6D4EvenTailTransformMoment 0
            (suzukiDF6D4EvenLowMode i) *
          suzukiDF6D4TailSmoothErrorCoefficient k +
        suzukiDF6D4EvenResidualTailFixedMoment 0 i *
          suzukiDF6D4TailFixedCoefficient 2 k := by
  unfold suzukiDF6D4EvenResidualTailOrderZeroRemainder
    suzukiDF6D4TailComparisonErrorCoefficient
    suzukiDF6D4TailSmoothErrorCoefficient
    suzukiDF6D4TailFixedCoefficient
  ring

theorem suzukiDF6D4OddResidualTailMain_eq_contribution
    (k : Nat) (i : Fin 44) :
    suzukiDF6D4OddResidualTailMain (601 + k) i =
      suzukiDF6D4OddResidualTailFixedMoment 0 i *
        suzukiDF6D4TailFixedCoefficient 1 k := by
  unfold suzukiDF6D4OddResidualTailMain
    suzukiDF6D4TailFixedCoefficient
  ring

theorem suzukiDF6D4OddResidualTailOrderZeroRemainder_eq_contributions
    (k : Nat) (i : Fin 44) :
    suzukiDF6D4OddResidualTailOrderZeroRemainder (601 + k) i =
      suzukiDF6D4OddResidualTailTransformMoment 0 i *
          suzukiDF6D4TailComparisonCoefficient 2 k +
        suzukiDF6D4OddTailTransformMoment 0
            (suzukiDF6D4OddLowMode i) *
          suzukiDF6D4TailDeltaCoefficient 2 k := by
  unfold suzukiDF6D4OddResidualTailOrderZeroRemainder
    suzukiDF6D4TailComparisonCoefficient
    suzukiDF6D4TailDeltaCoefficient
  ring

/-! ## Rank-one quadratic consumers -/

theorem suzukiDF6D4TailComparisonRankOne_summable
    {d : Nat} (vector x : Fin d → Real) (power : Nat) (hpower : 1 ≤ power) :
    Summable fun k : Nat =>
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailComparisonCoefficient power k) ^ 2 :=
  suzukiDF6D4RankOneCoefficientTail_summable
    (suzukiDF6D4TailComparisonCoefficient power) vector x
    (Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound) power
    (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      suzukiDF6D4ComparisonTailTransformBound_nonneg)
    hpower (suzukiDF6D4TailComparisonCoefficient_abs_le power)

theorem suzukiDF6D4TailDeltaRankOne_summable
    {d : Nat} (vector x : Fin d → Real) (power : Nat) (hpower : 1 ≤ power) :
    Summable fun k : Nat =>
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailDeltaCoefficient power k) ^ 2 :=
  suzukiDF6D4RankOneCoefficientTail_summable
    (suzukiDF6D4TailDeltaCoefficient power) vector x
    (Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound) power
    (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      suzukiDF6D4DeltaTailTransformBound_nonneg)
    hpower (suzukiDF6D4TailDeltaCoefficient_abs_le power)

theorem suzukiDF6D4TailFixedRankOne_summable
    {d : Nat} (vector x : Fin d → Real) (power : Nat) (hpower : 1 ≤ power) :
    Summable fun k : Nat =>
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailFixedCoefficient power k) ^ 2 :=
  suzukiDF6D4RankOneCoefficientTail_summable
    (suzukiDF6D4TailFixedCoefficient power) vector x Real.pi⁻¹ power
    (inv_nonneg.mpr Real.pi_pos.le) hpower
    (suzukiDF6D4TailFixedCoefficient_abs_le power)

theorem suzukiDF6D4TailComparisonErrorRankOne_summable
    {d : Nat} (vector x : Fin d → Real) :
    Summable fun k : Nat =>
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailComparisonErrorCoefficient k) ^ 2 :=
  suzukiDF6D4RankOneCoefficientTail_summable
    suzukiDF6D4TailComparisonErrorCoefficient vector x
    (Real.pi⁻¹ ^ 2) 2 (sq_nonneg _) (by norm_num)
    suzukiDF6D4TailComparisonErrorCoefficient_abs_le

theorem suzukiDF6D4TailSmoothErrorRankOne_summable
    {d : Nat} (vector x : Fin d → Real) :
    Summable fun k : Nat =>
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailSmoothErrorCoefficient k) ^ 2 :=
  suzukiDF6D4RankOneCoefficientTail_summable
    suzukiDF6D4TailSmoothErrorCoefficient vector x
    (Real.pi⁻¹ * suzukiDF6D4SmoothTailCoefficient) 2
    (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      suzukiDF6D4SmoothTailCoefficient_nonneg)
    (by norm_num) suzukiDF6D4TailSmoothErrorCoefficient_abs_le

theorem suzukiDF6D4TailComparisonRankOneQuadratic_le
    {d : Nat} (vector x : Fin d → Real) (power : Nat) (hpower : 1 ≤ power) :
    (∑' k : Nat,
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailComparisonCoefficient power k) ^ 2) ≤
      ((Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound) ^ 2 /
          (((2 * power - 1 : Nat) : Real) *
            (600 : Real) ^ (2 * power - 1))) *
        (∑ i, x i * vector i) ^ 2 := by
  exact suzukiDF6D4RankOneCoefficientTailQuadratic_le
    (suzukiDF6D4TailComparisonCoefficient power) vector x
    (Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound) power
    (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      suzukiDF6D4ComparisonTailTransformBound_nonneg)
    hpower (suzukiDF6D4TailComparisonCoefficient_abs_le power)

theorem suzukiDF6D4TailDeltaRankOneQuadratic_le
    {d : Nat} (vector x : Fin d → Real) (power : Nat) (hpower : 1 ≤ power) :
    (∑' k : Nat,
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailDeltaCoefficient power k) ^ 2) ≤
      ((Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound) ^ 2 /
          (((2 * power - 1 : Nat) : Real) *
            (600 : Real) ^ (2 * power - 1))) *
        (∑ i, x i * vector i) ^ 2 := by
  exact suzukiDF6D4RankOneCoefficientTailQuadratic_le
    (suzukiDF6D4TailDeltaCoefficient power) vector x
    (Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound) power
    (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      suzukiDF6D4DeltaTailTransformBound_nonneg)
    hpower (suzukiDF6D4TailDeltaCoefficient_abs_le power)

theorem suzukiDF6D4TailFixedRankOneQuadratic_le
    {d : Nat} (vector x : Fin d → Real) (power : Nat) (hpower : 1 ≤ power) :
    (∑' k : Nat,
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailFixedCoefficient power k) ^ 2) ≤
      ((Real.pi⁻¹) ^ 2 /
          (((2 * power - 1 : Nat) : Real) *
            (600 : Real) ^ (2 * power - 1))) *
        (∑ i, x i * vector i) ^ 2 := by
  exact suzukiDF6D4RankOneCoefficientTailQuadratic_le
    (suzukiDF6D4TailFixedCoefficient power) vector x Real.pi⁻¹ power
    (inv_nonneg.mpr Real.pi_pos.le) hpower
    (suzukiDF6D4TailFixedCoefficient_abs_le power)

theorem suzukiDF6D4TailComparisonErrorRankOneQuadratic_le
    {d : Nat} (vector x : Fin d → Real) :
    (∑' k : Nat,
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailComparisonErrorCoefficient k) ^ 2) ≤
      ((Real.pi⁻¹ ^ 2) ^ 2 /
          (3 * (600 : Real) ^ 3)) *
        (∑ i, x i * vector i) ^ 2 := by
  simpa only [Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat] using
    suzukiDF6D4RankOneCoefficientTailQuadratic_le
      suzukiDF6D4TailComparisonErrorCoefficient vector x
      (Real.pi⁻¹ ^ 2) 2 (sq_nonneg _) (by norm_num)
      suzukiDF6D4TailComparisonErrorCoefficient_abs_le

theorem suzukiDF6D4TailSmoothErrorRankOneQuadratic_le
    {d : Nat} (vector x : Fin d → Real) :
    (∑' k : Nat,
      ((∑ i, x i * vector i) *
        suzukiDF6D4TailSmoothErrorCoefficient k) ^ 2) ≤
      ((Real.pi⁻¹ * suzukiDF6D4SmoothTailCoefficient) ^ 2 /
          (3 * (600 : Real) ^ 3)) *
        (∑ i, x i * vector i) ^ 2 := by
  simpa only [Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat] using
    suzukiDF6D4RankOneCoefficientTailQuadratic_le
      suzukiDF6D4TailSmoothErrorCoefficient vector x
      (Real.pi⁻¹ * suzukiDF6D4SmoothTailCoefficient) 2
      (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
        suzukiDF6D4SmoothTailCoefficient_nonneg)
      (by norm_num) suzukiDF6D4TailSmoothErrorCoefficient_abs_le

/-! ## Finite structured contribution families -/

/-- The fifteen even structured contributions: three order-zero corrections
followed by three contributions for each order `1,...,4`. -/
def suzukiDF6D4EvenStructuredTailContribution
    (index : Fin 15) (k : Nat) (i : Fin 45) : Real :=
  let order := index.val / 3
  let slot := index.val % 3
  if order = 0 then
    if slot = 0 then
      suzukiDF6D4EvenResidualTailTransformMoment 0 i *
        suzukiDF6D4TailComparisonErrorCoefficient k
    else if slot = 1 then
      suzukiDF6D4EvenTailTransformMoment 0
          (suzukiDF6D4EvenLowMode i) *
        suzukiDF6D4TailSmoothErrorCoefficient k
    else
      suzukiDF6D4EvenResidualTailFixedMoment 0 i *
        suzukiDF6D4TailFixedCoefficient 2 k
  else if slot = 0 then
    suzukiDF6D4EvenResidualTailTransformMoment order i *
      suzukiDF6D4TailComparisonCoefficient (2 * order + 1) k
  else if slot = 1 then
    suzukiDF6D4EvenTailTransformMoment order
        (suzukiDF6D4EvenLowMode i) *
      suzukiDF6D4TailDeltaCoefficient (2 * order + 1) k
  else
    suzukiDF6D4EvenResidualTailFixedMoment order i *
      suzukiDF6D4TailFixedCoefficient (2 * order + 2) k

/-- The fourteen odd structured contributions: two order-zero transform
corrections followed by three contributions for each order `1,...,4`. -/
def suzukiDF6D4OddStructuredTailContribution
    (index : Fin 14) (k : Nat) (i : Fin 44) : Real :=
  if index.val = 0 then
    suzukiDF6D4OddResidualTailTransformMoment 0 i *
      suzukiDF6D4TailComparisonCoefficient 2 k
  else if index.val = 1 then
    suzukiDF6D4OddTailTransformMoment 0 (suzukiDF6D4OddLowMode i) *
      suzukiDF6D4TailDeltaCoefficient 2 k
  else
    let order := 1 + (index.val - 2) / 3
    let slot := (index.val - 2) % 3
    if slot = 0 then
      suzukiDF6D4OddResidualTailTransformMoment order i *
        suzukiDF6D4TailComparisonCoefficient (2 * order + 2) k
    else if slot = 1 then
      suzukiDF6D4OddTailTransformMoment order
          (suzukiDF6D4OddLowMode i) *
        suzukiDF6D4TailDeltaCoefficient (2 * order + 2) k
    else
      suzukiDF6D4OddResidualTailFixedMoment order i *
        suzukiDF6D4TailFixedCoefficient (2 * order + 1) k

def suzukiDF6D4EvenStructuredResidualTail
    (k : Nat) (i : Fin 45) : Real :=
  ∑ index : Fin 15, suzukiDF6D4EvenStructuredTailContribution index k i

def suzukiDF6D4OddStructuredResidualTail
    (k : Nat) (i : Fin 44) : Real :=
  ∑ index : Fin 14, suzukiDF6D4OddStructuredTailContribution index k i

theorem suzukiDF6D4EvenResidualTailPrefix_eq_main_add_structured
    (k : Nat) (i : Fin 45) :
    suzukiDF6D4EvenResidualTailPrefix (601 + k) i =
      suzukiDF6D4EvenResidualTailMain (601 + k) i +
        suzukiDF6D4EvenStructuredResidualTail k i := by
  rw [suzukiDF6D4EvenResidualTailPrefix_eq_sum_components]
  simp only [Finset.sum_range_succ, Finset.sum_insert,
    Finset.mem_range, not_false_eq_true, Finset.sum_empty, add_zero]
  rw [suzukiDF6D4EvenResidualTailComponent_zero_eq_main_add_remainder
    (601 + k) (by omega) i]
  rw [suzukiDF6D4EvenResidualTailOrderZeroRemainder_eq_contributions]
  rw [suzukiDF6D4EvenResidualTailComponent_eq_contributions 1]
  rw [suzukiDF6D4EvenResidualTailComponent_eq_contributions 2]
  rw [suzukiDF6D4EvenResidualTailComponent_eq_contributions 3]
  rw [suzukiDF6D4EvenResidualTailComponent_eq_contributions 4]
  unfold suzukiDF6D4EvenStructuredResidualTail
  simp [Fin.sum_univ_succ, suzukiDF6D4EvenStructuredTailContribution]
  ring

theorem suzukiDF6D4OddResidualTailPrefix_eq_main_add_structured
    (k : Nat) (i : Fin 44) :
    suzukiDF6D4OddResidualTailPrefix (601 + k) i =
      suzukiDF6D4OddResidualTailMain (601 + k) i +
        suzukiDF6D4OddStructuredResidualTail k i := by
  rw [suzukiDF6D4OddResidualTailPrefix_eq_sum_components]
  simp only [Finset.sum_range_succ, Finset.sum_insert,
    Finset.mem_range, not_false_eq_true, Finset.sum_empty, add_zero]
  rw [suzukiDF6D4OddResidualTailComponent_zero_eq_main_add_remainder
    (601 + k) (by omega) i]
  rw [suzukiDF6D4OddResidualTailOrderZeroRemainder_eq_contributions]
  rw [suzukiDF6D4OddResidualTailComponent_eq_contributions 1]
  rw [suzukiDF6D4OddResidualTailComponent_eq_contributions 2]
  rw [suzukiDF6D4OddResidualTailComponent_eq_contributions 3]
  rw [suzukiDF6D4OddResidualTailComponent_eq_contributions 4]
  unfold suzukiDF6D4OddStructuredResidualTail
  simp [Fin.sum_univ_succ, suzukiDF6D4OddStructuredTailContribution]
  ring

/-! ## Structured quadratic bounds -/

def suzukiDF6D4TailComparisonRankOneBound
    {d : Nat} (vector x : Fin d → Real) (power : Nat) : Real :=
  ((Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound) ^ 2 /
      (((2 * power - 1 : Nat) : Real) *
        (600 : Real) ^ (2 * power - 1))) *
    (∑ i, x i * vector i) ^ 2

def suzukiDF6D4TailDeltaRankOneBound
    {d : Nat} (vector x : Fin d → Real) (power : Nat) : Real :=
  ((Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound) ^ 2 /
      (((2 * power - 1 : Nat) : Real) *
        (600 : Real) ^ (2 * power - 1))) *
    (∑ i, x i * vector i) ^ 2

def suzukiDF6D4TailFixedRankOneBound
    {d : Nat} (vector x : Fin d → Real) (power : Nat) : Real :=
  ((Real.pi⁻¹) ^ 2 /
      (((2 * power - 1 : Nat) : Real) *
        (600 : Real) ^ (2 * power - 1))) *
    (∑ i, x i * vector i) ^ 2

def suzukiDF6D4TailComparisonErrorRankOneBound
    {d : Nat} (vector x : Fin d → Real) : Real :=
  ((Real.pi⁻¹ ^ 2) ^ 2 / (3 * (600 : Real) ^ 3)) *
    (∑ i, x i * vector i) ^ 2

def suzukiDF6D4TailSmoothErrorRankOneBound
    {d : Nat} (vector x : Fin d → Real) : Real :=
  ((Real.pi⁻¹ * suzukiDF6D4SmoothTailCoefficient) ^ 2 /
      (3 * (600 : Real) ^ 3)) *
    (∑ i, x i * vector i) ^ 2

private theorem suzukiDF6D4_dot_mul_coefficient
    {d : Nat} (x vector : Fin d → Real) (coefficient : Real) :
    (∑ i, x i * (vector i * coefficient)) =
      (∑ i, x i * vector i) * coefficient := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

def suzukiDF6D4EvenStructuredTailContributionBound
    (index : Fin 15) (x : Fin 45 → Real) : Real :=
  let order := index.val / 3
  let slot := index.val % 3
  if order = 0 then
    if slot = 0 then
      suzukiDF6D4TailComparisonErrorRankOneBound
        (suzukiDF6D4EvenResidualTailTransformMoment 0) x
    else if slot = 1 then
      suzukiDF6D4TailSmoothErrorRankOneBound
        (fun i => suzukiDF6D4EvenTailTransformMoment 0
          (suzukiDF6D4EvenLowMode i)) x
    else
      suzukiDF6D4TailFixedRankOneBound
        (suzukiDF6D4EvenResidualTailFixedMoment 0) x 2
  else if slot = 0 then
    suzukiDF6D4TailComparisonRankOneBound
      (suzukiDF6D4EvenResidualTailTransformMoment order) x
      (2 * order + 1)
  else if slot = 1 then
    suzukiDF6D4TailDeltaRankOneBound
      (fun i => suzukiDF6D4EvenTailTransformMoment order
        (suzukiDF6D4EvenLowMode i)) x (2 * order + 1)
  else
    suzukiDF6D4TailFixedRankOneBound
      (suzukiDF6D4EvenResidualTailFixedMoment order) x
      (2 * order + 2)

theorem suzukiDF6D4EvenStructuredTailContributionQuadratic_le
    (index : Fin 15) (x : Fin 45 → Real) :
    (∑' k : Nat,
      (∑ i, x i *
        suzukiDF6D4EvenStructuredTailContribution index k i) ^ 2) ≤
      suzukiDF6D4EvenStructuredTailContributionBound index x := by
  fin_cases index <;>
    simp only [suzukiDF6D4EvenStructuredTailContribution,
      suzukiDF6D4EvenStructuredTailContributionBound,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceEqDiff, if_false, if_true] <;>
    simp_rw [suzukiDF6D4_dot_mul_coefficient] <;>
    first
    | exact suzukiDF6D4TailComparisonErrorRankOneQuadratic_le _ _
    | exact suzukiDF6D4TailSmoothErrorRankOneQuadratic_le _ _
    | exact suzukiDF6D4TailComparisonRankOneQuadratic_le _ _ _ (by norm_num)
    | exact suzukiDF6D4TailDeltaRankOneQuadratic_le _ _ _ (by norm_num)
    | exact suzukiDF6D4TailFixedRankOneQuadratic_le _ _ _ (by norm_num)

def suzukiDF6D4OddStructuredTailContributionBound
    (index : Fin 14) (x : Fin 44 → Real) : Real :=
  if index.val = 0 then
    suzukiDF6D4TailComparisonRankOneBound
      (suzukiDF6D4OddResidualTailTransformMoment 0) x 2
  else if index.val = 1 then
    suzukiDF6D4TailDeltaRankOneBound
      (fun i => suzukiDF6D4OddTailTransformMoment 0
        (suzukiDF6D4OddLowMode i)) x 2
  else
    let order := 1 + (index.val - 2) / 3
    let slot := (index.val - 2) % 3
    if slot = 0 then
      suzukiDF6D4TailComparisonRankOneBound
        (suzukiDF6D4OddResidualTailTransformMoment order) x
        (2 * order + 2)
    else if slot = 1 then
      suzukiDF6D4TailDeltaRankOneBound
        (fun i => suzukiDF6D4OddTailTransformMoment order
          (suzukiDF6D4OddLowMode i)) x (2 * order + 2)
    else
      suzukiDF6D4TailFixedRankOneBound
        (suzukiDF6D4OddResidualTailFixedMoment order) x
        (2 * order + 1)

theorem suzukiDF6D4OddStructuredTailContributionQuadratic_le
    (index : Fin 14) (x : Fin 44 → Real) :
    (∑' k : Nat,
      (∑ i, x i *
        suzukiDF6D4OddStructuredTailContribution index k i) ^ 2) ≤
      suzukiDF6D4OddStructuredTailContributionBound index x := by
  fin_cases index <;>
    simp only [suzukiDF6D4OddStructuredTailContribution,
      suzukiDF6D4OddStructuredTailContributionBound,
      Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceEqDiff, if_false, if_true] <;>
    simp_rw [suzukiDF6D4_dot_mul_coefficient] <;>
    first
    | exact suzukiDF6D4TailComparisonRankOneQuadratic_le _ _ _ (by norm_num)
    | exact suzukiDF6D4TailDeltaRankOneQuadratic_le _ _ _ (by norm_num)
    | exact suzukiDF6D4TailFixedRankOneQuadratic_le _ _ _ (by norm_num)

set_option maxHeartbeats 600000 in
theorem suzukiDF6D4EvenStructuredTailContribution_summable
    (index : Fin 15) (x : Fin 45 → Real) :
    Summable fun k : Nat =>
      (∑ i, x i *
        suzukiDF6D4EvenStructuredTailContribution index k i) ^ 2 := by
  by_cases horder : index.val / 3 = 0
  · by_cases hslotZero : index.val % 3 = 0
    · simp only [suzukiDF6D4EvenStructuredTailContribution, horder,
        hslotZero, if_true]
      simp_rw [suzukiDF6D4_dot_mul_coefficient]
      exact suzukiDF6D4TailComparisonErrorRankOne_summable
        (suzukiDF6D4EvenResidualTailTransformMoment 0) x
    · by_cases hslotOne : index.val % 3 = 1
      · simp only [suzukiDF6D4EvenStructuredTailContribution, horder,
          hslotZero, hslotOne, Nat.reduceEqDiff, if_false, if_true]
        simp_rw [suzukiDF6D4_dot_mul_coefficient]
        exact suzukiDF6D4TailSmoothErrorRankOne_summable
          (fun i => suzukiDF6D4EvenTailTransformMoment 0
            (suzukiDF6D4EvenLowMode i)) x
      · simp only [suzukiDF6D4EvenStructuredTailContribution, horder,
          hslotZero, hslotOne, Nat.reduceEqDiff, if_false, if_true]
        simp_rw [suzukiDF6D4_dot_mul_coefficient]
        exact suzukiDF6D4TailFixedRankOne_summable
          (suzukiDF6D4EvenResidualTailFixedMoment 0) x 2 (by norm_num)
  · by_cases hslotZero : index.val % 3 = 0
    · simp only [suzukiDF6D4EvenStructuredTailContribution, horder,
        hslotZero, if_false, if_true]
      simp_rw [suzukiDF6D4_dot_mul_coefficient]
      exact suzukiDF6D4TailComparisonRankOne_summable
        (suzukiDF6D4EvenResidualTailTransformMoment (index.val / 3)) x
        (2 * (index.val / 3) + 1) (by omega)
    · by_cases hslotOne : index.val % 3 = 1
      · simp only [suzukiDF6D4EvenStructuredTailContribution, horder,
          hslotZero, hslotOne, Nat.reduceEqDiff, if_false, if_true]
        simp_rw [suzukiDF6D4_dot_mul_coefficient]
        exact suzukiDF6D4TailDeltaRankOne_summable
          (fun i => suzukiDF6D4EvenTailTransformMoment (index.val / 3)
            (suzukiDF6D4EvenLowMode i)) x
          (2 * (index.val / 3) + 1) (by omega)
      · simp only [suzukiDF6D4EvenStructuredTailContribution, horder,
          hslotZero, hslotOne, if_false, if_true]
        simp_rw [suzukiDF6D4_dot_mul_coefficient]
        exact suzukiDF6D4TailFixedRankOne_summable
          (suzukiDF6D4EvenResidualTailFixedMoment (index.val / 3)) x
          (2 * (index.val / 3) + 2) (by omega)

set_option maxHeartbeats 600000 in
theorem suzukiDF6D4OddStructuredTailContribution_summable
    (index : Fin 14) (x : Fin 44 → Real) :
    Summable fun k : Nat =>
      (∑ i, x i *
        suzukiDF6D4OddStructuredTailContribution index k i) ^ 2 := by
  by_cases hzero : index.val = 0
  · simp only [suzukiDF6D4OddStructuredTailContribution, hzero, if_true]
    simp_rw [suzukiDF6D4_dot_mul_coefficient]
    exact suzukiDF6D4TailComparisonRankOne_summable
      (suzukiDF6D4OddResidualTailTransformMoment 0) x 2 (by norm_num)
  · by_cases hone : index.val = 1
    · simp only [suzukiDF6D4OddStructuredTailContribution, hzero, hone,
        Nat.reduceEqDiff, if_false, if_true]
      simp_rw [suzukiDF6D4_dot_mul_coefficient]
      exact suzukiDF6D4TailDeltaRankOne_summable
        (fun i => suzukiDF6D4OddTailTransformMoment 0
          (suzukiDF6D4OddLowMode i)) x 2 (by norm_num)
    · by_cases hslotZero : (index.val - 2) % 3 = 0
      · simp only [suzukiDF6D4OddStructuredTailContribution, hzero, hone,
          hslotZero, if_false, if_true]
        simp_rw [suzukiDF6D4_dot_mul_coefficient]
        exact suzukiDF6D4TailComparisonRankOne_summable
          (suzukiDF6D4OddResidualTailTransformMoment
            (1 + (index.val - 2) / 3)) x
          (2 * (1 + (index.val - 2) / 3) + 2) (by omega)
      · by_cases hslotOne : (index.val - 2) % 3 = 1
        · simp only [suzukiDF6D4OddStructuredTailContribution, hzero, hone,
            hslotZero, hslotOne, Nat.reduceEqDiff, if_false, if_true]
          simp_rw [suzukiDF6D4_dot_mul_coefficient]
          exact suzukiDF6D4TailDeltaRankOne_summable
            (fun i => suzukiDF6D4OddTailTransformMoment
              (1 + (index.val - 2) / 3) (suzukiDF6D4OddLowMode i)) x
            (2 * (1 + (index.val - 2) / 3) + 2) (by omega)
        · simp only [suzukiDF6D4OddStructuredTailContribution, hzero, hone,
            hslotZero, hslotOne, if_false, if_true]
          simp_rw [suzukiDF6D4_dot_mul_coefficient]
          exact suzukiDF6D4TailFixedRankOne_summable
            (suzukiDF6D4OddResidualTailFixedMoment
              (1 + (index.val - 2) / 3)) x
            (2 * (1 + (index.val - 2) / 3) + 1) (by omega)

private theorem suzukiDF6D4_dot_fin_sum_sq_le
    {m d : Nat} (x : Fin d → Real) (vectors : Fin m → Fin d → Real) :
    (∑ i, x i * ∑ index, vectors index i) ^ 2 ≤
      (m : Real) * ∑ index, (∑ i, x i * vectors index i) ^ 2 := by
  have hdot :
      (∑ i, x i * ∑ index, vectors index i) =
        ∑ index, ∑ i, x i * vectors index i := by
    calc
      (∑ i, x i * ∑ index, vectors index i) =
          ∑ i, ∑ index, x i * vectors index i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ index, ∑ i, x i * vectors index i := Finset.sum_comm
  rw [hdot]
  simpa using
    (sq_sum_le_card_mul_sum_sq
      (s := Finset.univ)
      (f := fun index : Fin m => ∑ i, x i * vectors index i))

theorem suzukiDF6D4EvenStructuredResidualTailQuadratic_le
    (x : Fin 45 → Real) :
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4EvenStructuredResidualTail k i) ^ 2) ≤
      15 * ∑ index : Fin 15,
        suzukiDF6D4EvenStructuredTailContributionBound index x := by
  let term := fun index : Fin 15 => fun k : Nat =>
    (∑ i, x i *
      suzukiDF6D4EvenStructuredTailContribution index k i) ^ 2
  have hterm : ∀ index : Fin 15, Summable (term index) := fun index =>
    suzukiDF6D4EvenStructuredTailContribution_summable index x
  have hsum : Summable fun k : Nat => ∑ index : Fin 15, term index k := by
    simpa only [Finset.mem_univ, forall_const] using
      (summable_sum (s := Finset.univ)
        (fun index _ => hterm index))
  have hmajor : Summable fun k : Nat =>
      (15 : Real) * ∑ index : Fin 15, term index k :=
    hsum.mul_left 15
  have hpoint : ∀ k : Nat,
      (∑ i, x i * suzukiDF6D4EvenStructuredResidualTail k i) ^ 2 ≤
        (15 : Real) * ∑ index : Fin 15, term index k := by
    intro k
    unfold suzukiDF6D4EvenStructuredResidualTail
    exact suzukiDF6D4_dot_fin_sum_sq_le x
      (fun index i => suzukiDF6D4EvenStructuredTailContribution index k i)
  have hleft : Summable fun k : Nat =>
      (∑ i, x i * suzukiDF6D4EvenStructuredResidualTail k i) ^ 2 :=
    hmajor.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
  calc
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4EvenStructuredResidualTail k i) ^ 2) ≤
        ∑' k : Nat, (15 : Real) * ∑ index : Fin 15, term index k :=
      hleft.tsum_le_tsum hpoint hmajor
    _ = 15 * ∑ index : Fin 15, ∑' k : Nat, term index k := by
      rw [tsum_mul_left]
      congr 1
      simpa only [Finset.mem_univ] using
        (Summable.tsum_finsetSum (s := Finset.univ)
          (fun index _ => hterm index))
    _ ≤ 15 * ∑ index : Fin 15,
        suzukiDF6D4EvenStructuredTailContributionBound index x := by
      gcongr with index
      exact suzukiDF6D4EvenStructuredTailContributionQuadratic_le index x

theorem suzukiDF6D4OddStructuredResidualTailQuadratic_le
    (x : Fin 44 → Real) :
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4OddStructuredResidualTail k i) ^ 2) ≤
      14 * ∑ index : Fin 14,
        suzukiDF6D4OddStructuredTailContributionBound index x := by
  let term := fun index : Fin 14 => fun k : Nat =>
    (∑ i, x i *
      suzukiDF6D4OddStructuredTailContribution index k i) ^ 2
  have hterm : ∀ index : Fin 14, Summable (term index) := fun index =>
    suzukiDF6D4OddStructuredTailContribution_summable index x
  have hsum : Summable fun k : Nat => ∑ index : Fin 14, term index k := by
    simpa only [Finset.mem_univ, forall_const] using
      (summable_sum (s := Finset.univ)
        (fun index _ => hterm index))
  have hmajor : Summable fun k : Nat =>
      (14 : Real) * ∑ index : Fin 14, term index k :=
    hsum.mul_left 14
  have hpoint : ∀ k : Nat,
      (∑ i, x i * suzukiDF6D4OddStructuredResidualTail k i) ^ 2 ≤
        (14 : Real) * ∑ index : Fin 14, term index k := by
    intro k
    unfold suzukiDF6D4OddStructuredResidualTail
    exact suzukiDF6D4_dot_fin_sum_sq_le x
      (fun index i => suzukiDF6D4OddStructuredTailContribution index k i)
  have hleft : Summable fun k : Nat =>
      (∑ i, x i * suzukiDF6D4OddStructuredResidualTail k i) ^ 2 :=
    hmajor.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
  calc
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4OddStructuredResidualTail k i) ^ 2) ≤
        ∑' k : Nat, (14 : Real) * ∑ index : Fin 14, term index k :=
      hleft.tsum_le_tsum hpoint hmajor
    _ = 14 * ∑ index : Fin 14, ∑' k : Nat, term index k := by
      rw [tsum_mul_left]
      congr 1
      simpa only [Finset.mem_univ] using
        (Summable.tsum_finsetSum (s := Finset.univ)
          (fun index _ => hterm index))
    _ ≤ 14 * ∑ index : Fin 14,
        suzukiDF6D4OddStructuredTailContributionBound index x := by
      gcongr with index
      exact suzukiDF6D4OddStructuredTailContributionQuadratic_le index x

end

end RiemannHypothesisProject.Experiments.M100
