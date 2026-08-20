import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailParity
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDirichletIntegral

/-!
# Coordinate expansion for the M100-DF6D4 residual tails

This module applies the shared five-term resolvent expansion to the exact even
and odd convolution kernels.  It keeps the fixed transform values and the
geometric remainder separate, matching the structured-coordinate split used
by the frozen FT3 and DF1 scripts.  Matrix and interval assembly remain in
later modules.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- Five-term even normalized kernel, before the parity and basis prefactors. -/
def suzukiDF6D4EvenNormalizedTailPrefix
    (m n Jm Jn : Real) : Real :=
  (Jn / n - m * Jm / n ^ 2) *
    suzukiDF6D4GeometricPrefix ((m / n) ^ 2) 4

/-- Exact even normalized-kernel remainder after the five-term prefix. -/
def suzukiDF6D4EvenNormalizedTailRemainder
    (m n Jm Jn : Real) : Real :=
  (Jn / n - m * Jm / n ^ 2) *
    (1 / (1 - (m / n) ^ 2) -
      suzukiDF6D4GeometricPrefix ((m / n) ^ 2) 4)

/-- Five-term odd normalized kernel, before the parity prefactor. -/
def suzukiDF6D4OddNormalizedTailPrefix
    (m n Jm Jn : Real) : Real :=
  (m * Jn / n ^ 2 - Jm / n) *
    suzukiDF6D4GeometricPrefix ((m / n) ^ 2) 4

/-- Exact odd normalized-kernel remainder after the five-term prefix. -/
def suzukiDF6D4OddNormalizedTailRemainder
    (m n Jm Jn : Real) : Real :=
  (m * Jn / n ^ 2 - Jm / n) *
    (1 / (1 - (m / n) ^ 2) -
      suzukiDF6D4GeometricPrefix ((m / n) ^ 2) 4)

theorem suzukiDF6D4EvenConvolutionKernel_eq_tailPrefix_add_remainder
    (m n Jm Jn : Real) (hn : n ≠ 0)
    (hsquare : n ^ 2 - m ^ 2 ≠ 0) :
    (n * Jn - m * Jm) / (n ^ 2 - m ^ 2) =
      suzukiDF6D4EvenNormalizedTailPrefix m n Jm Jn +
        suzukiDF6D4EvenNormalizedTailRemainder m n Jm Jn := by
  rw [suzukiDF6D4EvenConvolutionKernel_normalized m n Jm Jn hn hsquare]
  unfold suzukiDF6D4EvenNormalizedTailPrefix
    suzukiDF6D4EvenNormalizedTailRemainder
  ring

theorem suzukiDF6D4OddConvolutionKernel_eq_tailPrefix_add_remainder
    (m n Jm Jn : Real) (hn : n ≠ 0)
    (hsquare : n ^ 2 - m ^ 2 ≠ 0) :
    (m * Jn - n * Jm) / (n ^ 2 - m ^ 2) =
      suzukiDF6D4OddNormalizedTailPrefix m n Jm Jn +
        suzukiDF6D4OddNormalizedTailRemainder m n Jm Jn := by
  rw [suzukiDF6D4OddConvolutionKernel_normalized m n Jm Jn hn hsquare]
  unfold suzukiDF6D4OddNormalizedTailPrefix
    suzukiDF6D4OddNormalizedTailRemainder
  ring

/-- Frozen coordinatewise bound for the even five-term geometric remainder. -/
theorem suzukiDF6D4EvenNormalizedTailRemainder_abs_le
    (m n : Nat) (Jm Jn : Real) (hm : m ≤ 300) (hn : 601 ≤ n) :
    |suzukiDF6D4EvenNormalizedTailRemainder m n Jm Jn| ≤
      |Jn / n - m * Jm / (n : Real) ^ 2| *
        ((((m : Real) / n) ^ 2) ^ 5 /
          (1 - (((m : Real) / 601) ^ 2))) := by
  unfold suzukiDF6D4EvenNormalizedTailRemainder
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (suzukiDF6D4FrozenOrderFourRatioRemainder_abs_le m n hm hn)
    (abs_nonneg _)

/-- Frozen coordinatewise bound for the odd five-term geometric remainder. -/
theorem suzukiDF6D4OddNormalizedTailRemainder_abs_le
    (m n : Nat) (Jm Jn : Real) (hm : m ≤ 300) (hn : 601 ≤ n) :
    |suzukiDF6D4OddNormalizedTailRemainder m n Jm Jn| ≤
      |m * Jn / (n : Real) ^ 2 - Jm / n| *
        ((((m : Real) / n) ^ 2) ^ 5 /
          (1 - (((m : Real) / 601) ^ 2))) := by
  unfold suzukiDF6D4OddNormalizedTailRemainder
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (suzukiDF6D4FrozenOrderFourRatioRemainder_abs_le m n hm hn)
    (abs_nonneg _)

/-- Frozen even coordinate envelope before the parity, basis, and `pi⁻¹`
prefactors. -/
def suzukiDF6D4EvenNormalizedGeometricEnvelope
    (m : Nat) (Jm transformBound : Real) : Real :=
  (m : Real) ^ 10 *
    (transformBound + (m : Real) * |Jm| / 601) /
      (1 - (((m : Real) / 601) ^ 2))

/-- Frozen odd coordinate envelope before the parity and `pi⁻¹` prefactors. -/
def suzukiDF6D4OddNormalizedGeometricEnvelope
    (m : Nat) (Jm transformBound : Real) : Real :=
  (m : Real) ^ 10 *
    (|Jm| + (m : Real) * transformBound / 601) /
      (1 - (((m : Real) / 601) ^ 2))

theorem suzukiDF6D4EvenNormalizedGeometricEnvelope_nonneg
    (m : Nat) (Jm transformBound : Real) (hm : m ≤ 300)
    (hbound : 0 ≤ transformBound) :
    0 ≤ suzukiDF6D4EvenNormalizedGeometricEnvelope m Jm transformBound := by
  have hm601 : (m : Real) < 601 := by exact_mod_cast hm.trans_lt (by norm_num)
  have hratio : (m : Real) / 601 < 1 := (div_lt_one (by norm_num)).2 hm601
  have hden : 0 < 1 - (((m : Real) / 601) ^ 2) := by
    nlinarith [sq_nonneg ((m : Real) / 601)]
  unfold suzukiDF6D4EvenNormalizedGeometricEnvelope
  positivity

theorem suzukiDF6D4OddNormalizedGeometricEnvelope_nonneg
    (m : Nat) (Jm transformBound : Real) (hm : m ≤ 300)
    (hbound : 0 ≤ transformBound) :
    0 ≤ suzukiDF6D4OddNormalizedGeometricEnvelope m Jm transformBound := by
  have hm601 : (m : Real) < 601 := by exact_mod_cast hm.trans_lt (by norm_num)
  have hratio : (m : Real) / 601 < 1 := (div_lt_one (by norm_num)).2 hm601
  have hden : 0 < 1 - (((m : Real) / 601) ^ 2) := by
    nlinarith [sq_nonneg ((m : Real) / 601)]
  unfold suzukiDF6D4OddNormalizedGeometricEnvelope
  positivity

private theorem even_base_abs_le
    (m n Jm Jn transformBound : Real)
    (hm : 0 ≤ m) (hn : 0 < n)
    (hJn : |Jn| ≤ transformBound) :
    |Jn / n - m * Jm / n ^ 2| ≤
      (transformBound + m * |Jm| / n) / n := by
  calc
    |Jn / n - m * Jm / n ^ 2| ≤
        |Jn / n| + |m * Jm / n ^ 2| := abs_sub _ _
    _ = |Jn| / n + m * |Jm| / n ^ 2 := by
      rw [abs_div, abs_div, abs_mul, abs_of_nonneg hm,
        abs_of_pos hn, abs_of_pos (pow_pos hn 2)]
    _ ≤ transformBound / n + m * |Jm| / n ^ 2 := by
      gcongr
    _ = (transformBound + m * |Jm| / n) / n := by
      field_simp [ne_of_gt hn]

private theorem odd_base_abs_le
    (m n Jm Jn transformBound : Real)
    (hm : 0 ≤ m) (hn : 0 < n)
    (hJn : |Jn| ≤ transformBound) :
    |m * Jn / n ^ 2 - Jm / n| ≤
      (|Jm| + m * transformBound / n) / n := by
  calc
    |m * Jn / n ^ 2 - Jm / n| ≤
        |m * Jn / n ^ 2| + |Jm / n| := abs_sub _ _
    _ = m * |Jn| / n ^ 2 + |Jm| / n := by
      rw [abs_div, abs_mul, abs_of_nonneg hm,
        abs_of_pos (pow_pos hn 2), abs_div, abs_of_pos hn]
    _ ≤ m * transformBound / n ^ 2 + |Jm| / n := by
      gcongr
    _ = (|Jm| + m * transformBound / n) / n := by
      field_simp [ne_of_gt hn]
      ring

theorem suzukiDF6D4EvenNormalizedTailRemainder_abs_le_orderEleven
    (m n : Nat) (Jm Jn transformBound : Real)
    (hm : m ≤ 300) (hn : 601 ≤ n) (_hbound : 0 ≤ transformBound)
    (hJn : |Jn| ≤ transformBound) :
    |suzukiDF6D4EvenNormalizedTailRemainder m n Jm Jn| ≤
      suzukiDF6D4EvenNormalizedGeometricEnvelope m Jm transformBound /
        (n : Real) ^ 11 := by
  have hnPos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hn601 : (601 : Real) ≤ n := by exact_mod_cast hn
  have hm601 : (m : Real) < 601 := by exact_mod_cast hm.trans_lt (by norm_num)
  have hden : 0 < 1 - (((m : Real) / 601) ^ 2) := by
    have hratio : (m : Real) / 601 < 1 := (div_lt_one (by norm_num)).2 hm601
    nlinarith [sq_nonneg ((m : Real) / 601)]
  have hbase := even_base_abs_le (m : Real) (n : Real) Jm Jn
    transformBound (by positivity) hnPos hJn
  have hinv : 1 / (n : Real) ≤ 1 / 601 := by
    exact one_div_le_one_div_of_le (by norm_num) hn601
  have hinner :
      transformBound + (m : Real) * |Jm| / n ≤
        transformBound + (m : Real) * |Jm| / 601 := by
    gcongr
  have hbaseFrozen :
      |Jn / n - (m : Real) * Jm / (n : Real) ^ 2| ≤
        (transformBound + (m : Real) * |Jm| / 601) / n :=
    hbase.trans (div_le_div_of_nonneg_right hinner hnPos.le)
  have hrem := suzukiDF6D4EvenNormalizedTailRemainder_abs_le
    m n Jm Jn hm hn
  calc
    |suzukiDF6D4EvenNormalizedTailRemainder m n Jm Jn| ≤
        |Jn / n - (m : Real) * Jm / (n : Real) ^ 2| *
          ((((m : Real) / n) ^ 2) ^ 5 /
            (1 - (((m : Real) / 601) ^ 2))) := hrem
    _ ≤ ((transformBound + (m : Real) * |Jm| / 601) / n) *
          ((((m : Real) / n) ^ 2) ^ 5 /
            (1 - (((m : Real) / 601) ^ 2))) := by
      gcongr
    _ = suzukiDF6D4EvenNormalizedGeometricEnvelope m Jm transformBound /
          (n : Real) ^ 11 := by
      unfold suzukiDF6D4EvenNormalizedGeometricEnvelope
      field_simp [ne_of_gt hnPos, ne_of_gt hden]

theorem suzukiDF6D4OddNormalizedTailRemainder_abs_le_orderEleven
    (m n : Nat) (Jm Jn transformBound : Real)
    (hm : m ≤ 300) (hn : 601 ≤ n) (hbound : 0 ≤ transformBound)
    (hJn : |Jn| ≤ transformBound) :
    |suzukiDF6D4OddNormalizedTailRemainder m n Jm Jn| ≤
      suzukiDF6D4OddNormalizedGeometricEnvelope m Jm transformBound /
        (n : Real) ^ 11 := by
  have hnPos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hn601 : (601 : Real) ≤ n := by exact_mod_cast hn
  have hm601 : (m : Real) < 601 := by exact_mod_cast hm.trans_lt (by norm_num)
  have hden : 0 < 1 - (((m : Real) / 601) ^ 2) := by
    have hratio : (m : Real) / 601 < 1 := (div_lt_one (by norm_num)).2 hm601
    nlinarith [sq_nonneg ((m : Real) / 601)]
  have hbase := odd_base_abs_le (m : Real) (n : Real) Jm Jn
    transformBound (by positivity) hnPos hJn
  have hinner :
      |Jm| + (m : Real) * transformBound / n ≤
        |Jm| + (m : Real) * transformBound / 601 := by
    gcongr
  have hbaseFrozen :
      |(m : Real) * Jn / (n : Real) ^ 2 - Jm / n| ≤
        (|Jm| + (m : Real) * transformBound / 601) / n :=
    hbase.trans (div_le_div_of_nonneg_right hinner hnPos.le)
  have hrem := suzukiDF6D4OddNormalizedTailRemainder_abs_le
    m n Jm Jn hm hn
  calc
    |suzukiDF6D4OddNormalizedTailRemainder m n Jm Jn| ≤
        |(m : Real) * Jn / (n : Real) ^ 2 - Jm / n| *
          ((((m : Real) / n) ^ 2) ^ 5 /
            (1 - (((m : Real) / 601) ^ 2))) := hrem
    _ ≤ ((|Jm| + (m : Real) * transformBound / 601) / n) *
          ((((m : Real) / n) ^ 2) ^ 5 /
            (1 - (((m : Real) / 601) ^ 2))) := by
      gcongr
    _ = suzukiDF6D4OddNormalizedGeometricEnvelope m Jm transformBound /
          (n : Real) ^ 11 := by
      unfold suzukiDF6D4OddNormalizedGeometricEnvelope
      field_simp [ne_of_gt hnPos, ne_of_gt hden]

/-! ## Concrete complete and comparison coordinates -/

def suzukiDF6D4EvenTailPrefix
    (transform : Nat → Real) (left right : Nat) : Real :=
  suzukiDF6D4EvenModeScale left *
      suzukiDF6D4EvenModeScale right * Real.pi⁻¹ *
    (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
      suzukiDF6D4EvenNormalizedTailPrefix left right
        (transform left) (transform right))

def suzukiDF6D4EvenTailRemainder
    (transform : Nat → Real) (left right : Nat) : Real :=
  suzukiDF6D4EvenModeScale left *
      suzukiDF6D4EvenModeScale right * Real.pi⁻¹ *
    (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
      suzukiDF6D4EvenNormalizedTailRemainder left right
        (transform left) (transform right))

def suzukiDF6D4OddTailPrefix
    (transform : Nat → Real) (left right : Nat) : Real :=
  Real.pi⁻¹ *
    (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
      suzukiDF6D4OddNormalizedTailPrefix left right
        (transform left) (transform right))

def suzukiDF6D4OddTailRemainder
    (transform : Nat → Real) (left right : Nat) : Real :=
  Real.pi⁻¹ *
    (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
      suzukiDF6D4OddNormalizedTailRemainder left right
        (transform left) (transform right))

/-- One of the five even structured coordinates in the frozen resolvent
prefix. -/
def suzukiDF6D4EvenTailComponent
    (transform : Nat → Real) (order left right : Nat) : Real :=
  suzukiDF6D4EvenModeScale left *
      suzukiDF6D4EvenModeScale right * Real.pi⁻¹ *
    (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
      ((transform right / right -
          (left : Real) * transform left / (right : Real) ^ 2) *
        ((((left : Real) / right) ^ 2) ^ order)))

/-- One of the five odd structured coordinates in the frozen resolvent
prefix. -/
def suzukiDF6D4OddTailComponent
    (transform : Nat → Real) (order left right : Nat) : Real :=
  Real.pi⁻¹ *
    (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
      ((((left : Real) * transform right / (right : Real) ^ 2 -
          transform left / right)) *
        ((((left : Real) / right) ^ 2) ^ order)))

theorem suzukiDF6D4EvenTailPrefix_eq_sum_components
    (transform : Nat → Real) (left right : Nat) :
    suzukiDF6D4EvenTailPrefix transform left right =
      ∑ order ∈ Finset.range 5,
        suzukiDF6D4EvenTailComponent transform order left right := by
  unfold suzukiDF6D4EvenTailPrefix
    suzukiDF6D4EvenNormalizedTailPrefix
    suzukiDF6D4GeometricPrefix
    suzukiDF6D4EvenTailComponent
  simp only [Nat.reduceAdd]
  repeat rw [Finset.mul_sum]

theorem suzukiDF6D4OddTailPrefix_eq_sum_components
    (transform : Nat → Real) (left right : Nat) :
    suzukiDF6D4OddTailPrefix transform left right =
      ∑ order ∈ Finset.range 5,
        suzukiDF6D4OddTailComponent transform order left right := by
  unfold suzukiDF6D4OddTailPrefix
    suzukiDF6D4OddNormalizedTailPrefix
    suzukiDF6D4GeometricPrefix
    suzukiDF6D4OddTailComponent
  simp only [Nat.reduceAdd]
  repeat rw [Finset.mul_sum]

/-- Moment-vector normal form of one even structured coordinate. -/
theorem suzukiDF6D4EvenTailComponent_eq_momentForm
    (transform : Nat → Real) (order left right : Nat) (hright : right ≠ 0) :
    suzukiDF6D4EvenTailComponent transform order left right =
      suzukiDF6D4EvenModeScale left *
          suzukiDF6D4EvenModeScale right * Real.pi⁻¹ *
        (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
          (((left : Real) ^ (2 * order) * transform right /
              (right : Real) ^ (2 * order + 1)) -
            ((left : Real) ^ (2 * order + 1) * transform left /
              (right : Real) ^ (2 * order + 2)))) := by
  unfold suzukiDF6D4EvenTailComponent
  have hrightReal : (right : Real) ≠ 0 := by exact_mod_cast hright
  rw [← pow_mul, div_pow]
  field_simp [hrightReal, pow_add]
  ring

/-- Moment-vector normal form of one odd structured coordinate. -/
theorem suzukiDF6D4OddTailComponent_eq_momentForm
    (transform : Nat → Real) (order left right : Nat) (hright : right ≠ 0) :
    suzukiDF6D4OddTailComponent transform order left right =
      Real.pi⁻¹ *
        (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
          (((left : Real) ^ (2 * order + 1) * transform right /
              (right : Real) ^ (2 * order + 2)) -
            ((left : Real) ^ (2 * order) * transform left /
              (right : Real) ^ (2 * order + 1)))) := by
  unfold suzukiDF6D4OddTailComponent
  have hrightReal : (right : Real) ≠ 0 := by exact_mod_cast hright
  rw [← pow_mul, div_pow]
  field_simp [hrightReal, pow_add]
  ring

def suzukiDF6D4EvenTailTransformMoment (order mode : Nat) : Real :=
  suzukiDF6D4EvenModeScale mode *
    (((suzukiDF6D4AlternatingSign mode : Rat) : Real)) *
      (mode : Real) ^ (2 * order)

def suzukiDF6D4EvenTailFixedMoment
    (transform : Nat → Real) (order mode : Nat) : Real :=
  suzukiDF6D4EvenModeScale mode *
    (((suzukiDF6D4AlternatingSign mode : Rat) : Real)) *
      (mode : Real) ^ (2 * order + 1) * transform mode

def suzukiDF6D4OddTailTransformMoment (order mode : Nat) : Real :=
  (((suzukiDF6D4AlternatingSign mode : Rat) : Real)) *
    (mode : Real) ^ (2 * order + 1)

def suzukiDF6D4OddTailFixedMoment
    (transform : Nat → Real) (order mode : Nat) : Real :=
  (((suzukiDF6D4AlternatingSign mode : Rat) : Real)) *
    (mode : Real) ^ (2 * order) * transform mode

/-- A fixed tail parity multiplies two row vectors in every even structured
component. -/
theorem suzukiDF6D4EvenTailComponent_eq_factoredMomentForm
    (transform : Nat → Real) (order left right : Nat)
    (hleftRight : left ≤ right) (hright : right ≠ 0) :
    suzukiDF6D4EvenTailComponent transform order left right =
      (((suzukiDF6D4TailParity right : Rat) : Real)) * Real.pi⁻¹ *
        (suzukiDF6D4EvenTailTransformMoment order left * transform right /
            (right : Real) ^ (2 * order + 1) -
          suzukiDF6D4EvenTailFixedMoment transform order left /
            (right : Real) ^ (2 * order + 2)) := by
  rw [suzukiDF6D4EvenTailComponent_eq_momentForm _ _ _ _ hright]
  have hscaleRight : suzukiDF6D4EvenModeScale right = 1 := by
    simp [suzukiDF6D4EvenModeScale, hright]
  rw [hscaleRight, suzukiDF6D4AlternatingSign_sub_factor
    left right hleftRight]
  push_cast
  unfold suzukiDF6D4EvenTailTransformMoment
    suzukiDF6D4EvenTailFixedMoment
  ring

/-- A fixed tail parity multiplies two row vectors in every odd structured
component. -/
theorem suzukiDF6D4OddTailComponent_eq_factoredMomentForm
    (transform : Nat → Real) (order left right : Nat)
    (hleftRight : left ≤ right) (hright : right ≠ 0) :
    suzukiDF6D4OddTailComponent transform order left right =
      (((suzukiDF6D4TailParity right : Rat) : Real)) * Real.pi⁻¹ *
        (suzukiDF6D4OddTailTransformMoment order left * transform right /
            (right : Real) ^ (2 * order + 2) -
          suzukiDF6D4OddTailFixedMoment transform order left /
            (right : Real) ^ (2 * order + 1)) := by
  rw [suzukiDF6D4OddTailComponent_eq_momentForm _ _ _ _ hright]
  rw [suzukiDF6D4AlternatingSign_sub_factor left right hleftRight]
  push_cast
  unfold suzukiDF6D4OddTailTransformMoment
    suzukiDF6D4OddTailFixedMoment
  ring

/-- Even order-`n^-11` envelope with all parity and basis prefactors included. -/
def suzukiDF6D4EvenGeometricEnvelope
    (transform : Nat → Real) (m : Nat) (transformBound : Real) : Real :=
  |suzukiDF6D4EvenModeScale m| * Real.pi⁻¹ *
    suzukiDF6D4EvenNormalizedGeometricEnvelope m
      (transform m) transformBound

/-- Odd order-`n^-11` envelope with the `pi⁻¹` prefactor included. -/
def suzukiDF6D4OddGeometricEnvelope
    (transform : Nat → Real) (m : Nat) (transformBound : Real) : Real :=
  Real.pi⁻¹ *
    suzukiDF6D4OddNormalizedGeometricEnvelope m
      (transform m) transformBound

theorem suzukiDF6D4EvenGeometricEnvelope_nonneg
    (transform : Nat → Real) (m : Nat) (transformBound : Real)
    (hm : m ≤ 300) (hbound : 0 ≤ transformBound) :
    0 ≤ suzukiDF6D4EvenGeometricEnvelope transform m transformBound := by
  unfold suzukiDF6D4EvenGeometricEnvelope
  exact mul_nonneg
    (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr Real.pi_pos.le))
    (suzukiDF6D4EvenNormalizedGeometricEnvelope_nonneg
      m (transform m) transformBound hm hbound)

theorem suzukiDF6D4OddGeometricEnvelope_nonneg
    (transform : Nat → Real) (m : Nat) (transformBound : Real)
    (hm : m ≤ 300) (hbound : 0 ≤ transformBound) :
    0 ≤ suzukiDF6D4OddGeometricEnvelope transform m transformBound := by
  unfold suzukiDF6D4OddGeometricEnvelope
  exact mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
    (suzukiDF6D4OddNormalizedGeometricEnvelope_nonneg
      m (transform m) transformBound hm hbound)

/-- Frozen comparison-transform amplitude used by both residual tails. -/
def suzukiDF6D4ComparisonTailTransformBound : Real :=
  Real.pi / 2 + 1 / (Real.pi * 601)

/-- Frozen complete-transform amplitude, including prime 2 and smooth
variation, used by both residual tails. -/
def suzukiDF6D4CompleteTailTransformBound : Real :=
  Real.pi / 2 + 1 / (Real.pi * 601) +
    Real.sqrt 2 * Real.log 2 +
      (2 * suzukiDF6D4RemainderVariationUpper * suzukiProjectAStar /
        Real.pi) / 601

theorem suzukiDF6D4ComparisonTailTransformBound_nonneg :
    0 ≤ suzukiDF6D4ComparisonTailTransformBound := by
  unfold suzukiDF6D4ComparisonTailTransformBound
  positivity

theorem suzukiDF6D4CompleteTailTransformBound_nonneg :
    0 ≤ suzukiDF6D4CompleteTailTransformBound := by
  have hvariation : 0 ≤ suzukiDF6D4RemainderVariationUpper := by
    norm_num [suzukiDF6D4RemainderVariationUpper]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hprime : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg 2) hlog
  have hsmooth :
      0 ≤ (2 * suzukiDF6D4RemainderVariationUpper * suzukiProjectAStar /
        Real.pi) / 601 := by
    exact div_nonneg
      (div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hvariation)
          suzukiProjectAStar_pos.le)
        Real.pi_pos.le)
      (by norm_num)
  have hcomparison := suzukiDF6D4ComparisonTailTransformBound_nonneg
  unfold suzukiDF6D4CompleteTailTransformBound
  unfold suzukiDF6D4ComparisonTailTransformBound at hcomparison
  linarith

theorem suzukiDF6D4ComparisonSineTransform_abs_le_frozen
    (mode : Nat) (hmode : 601 ≤ mode) :
    |suzukiDF6D4ComparisonSineTransform mode| ≤
      suzukiDF6D4ComparisonTailTransformBound := by
  have hmodeReal : (601 : Real) ≤ mode := by exact_mod_cast hmode
  have hdenom :
      1 / (Real.pi * mode) ≤ 1 / (Real.pi * 601) := by
    exact div_le_div_of_nonneg_left (by norm_num)
      (mul_pos Real.pi_pos (by norm_num))
      (mul_le_mul_of_nonneg_left hmodeReal Real.pi_pos.le)
  have h := suzukiDF6D4ComparisonSineTransform_abs_le mode (by omega)
  unfold suzukiDF6D4ComparisonTailTransformBound
  linarith

theorem suzukiDF6D4CompleteSineTransform_abs_le_tailBound
    (mode : Nat) (hmode : 601 ≤ mode) :
    |suzukiDF6D4CompleteSineTransform mode| ≤
      suzukiDF6D4CompleteTailTransformBound := by
  simpa only [suzukiDF6D4CompleteTailTransformBound] using
    suzukiDF6D4CompleteSineTransform_abs_le_frozen mode hmode

theorem suzukiDF6D4EvenTailRemainder_abs_le_orderEleven
    (transform : Nat → Real) (m n : Nat) (transformBound : Real)
    (hm : m ≤ 300) (hn : 601 ≤ n) (hbound : 0 ≤ transformBound)
    (htransform : |transform n| ≤ transformBound) :
    |suzukiDF6D4EvenTailRemainder transform m n| ≤
      suzukiDF6D4EvenGeometricEnvelope transform m transformBound /
        (n : Real) ^ 11 := by
  have hnNe : n ≠ 0 := by omega
  have hscaleN : suzukiDF6D4EvenModeScale n = 1 := by
    simp [suzukiDF6D4EvenModeScale, hnNe]
  have hnormal :=
    suzukiDF6D4EvenNormalizedTailRemainder_abs_le_orderEleven
      m n (transform m) (transform n) transformBound hm hn hbound htransform
  unfold suzukiDF6D4EvenTailRemainder
    suzukiDF6D4EvenGeometricEnvelope
  rw [abs_mul, abs_mul, abs_mul, abs_mul, hscaleN, abs_one,
    suzukiDF6D4AlternatingSign_real_abs, abs_inv,
    abs_of_pos Real.pi_pos]
  have hfactor :
      0 ≤ |suzukiDF6D4EvenModeScale m| * Real.pi⁻¹ :=
    mul_nonneg (abs_nonneg _) (inv_nonneg.mpr Real.pi_pos.le)
  simpa only [mul_one, one_mul, div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left hnormal hfactor

theorem suzukiDF6D4OddTailRemainder_abs_le_orderEleven
    (transform : Nat → Real) (m n : Nat) (transformBound : Real)
    (hm : m ≤ 300) (hn : 601 ≤ n) (hbound : 0 ≤ transformBound)
    (htransform : |transform n| ≤ transformBound) :
    |suzukiDF6D4OddTailRemainder transform m n| ≤
      suzukiDF6D4OddGeometricEnvelope transform m transformBound /
        (n : Real) ^ 11 := by
  have hnormal :=
    suzukiDF6D4OddNormalizedTailRemainder_abs_le_orderEleven
      m n (transform m) (transform n) transformBound hm hn hbound htransform
  unfold suzukiDF6D4OddTailRemainder
    suzukiDF6D4OddGeometricEnvelope
  rw [abs_mul, abs_mul, suzukiDF6D4AlternatingSign_real_abs,
    abs_inv, abs_of_pos Real.pi_pos]
  simpa only [mul_one, one_mul, div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left hnormal (inv_nonneg.mpr Real.pi_pos.le)

private theorem square_sub_ne_zero_of_nat_lt
    (left right : Nat) (hleftRight : left < right) :
    (right : Real) ^ 2 - (left : Real) ^ 2 ≠ 0 := by
  have hright : (left : Real) < right := by exact_mod_cast hleftRight
  nlinarith [sq_nonneg ((right : Real) + left)]

theorem suzukiDF6D4EvenOffDiagonal_eq_tailPrefix_add_remainder
    (left right : Nat) (hleftRight : left < right) :
    suzukiDF6D4EvenOffDiagonal left right =
      suzukiDF6D4EvenTailPrefix suzukiDF6D4CompleteSineTransform left right +
        suzukiDF6D4EvenTailRemainder
          suzukiDF6D4CompleteSineTransform left right := by
  rw [suzukiDF6D4EvenOffDiagonal_eq_signedNormalizedKernel
    left right hleftRight]
  rw [suzukiDF6D4EvenConvolutionKernel_eq_tailPrefix_add_remainder
    (left : Real) (right : Real)
    (suzukiDF6D4CompleteSineTransform left)
    (suzukiDF6D4CompleteSineTransform right)
    (by exact_mod_cast (by omega : right ≠ 0))
    (square_sub_ne_zero_of_nat_lt left right hleftRight)]
  unfold suzukiDF6D4EvenTailPrefix suzukiDF6D4EvenTailRemainder
  ring

theorem suzukiDF6D4ComparisonEvenOffDiagonal_eq_tailPrefix_add_remainder
    (left right : Nat) (hleftPos : 0 < left) (hleftRight : left < right) :
    suzukiDF6D4ComparisonEvenOffDiagonal left right =
      suzukiDF6D4EvenTailPrefix suzukiDF6D4ComparisonSineTransform left right +
        suzukiDF6D4EvenTailRemainder
          suzukiDF6D4ComparisonSineTransform left right := by
  rw [suzukiDF6D4ComparisonEvenOffDiagonal_eq_signedNormalizedKernel
    left right hleftPos hleftRight]
  rw [suzukiDF6D4EvenConvolutionKernel_eq_tailPrefix_add_remainder
    (left : Real) (right : Real)
    (suzukiDF6D4ComparisonSineTransform left)
    (suzukiDF6D4ComparisonSineTransform right)
    (by exact_mod_cast (by omega : right ≠ 0))
    (square_sub_ne_zero_of_nat_lt left right hleftRight)]
  unfold suzukiDF6D4EvenTailPrefix suzukiDF6D4EvenTailRemainder
  ring

theorem suzukiDF6D4OddOffDiagonal_eq_tailPrefix_add_remainder
    (left right : Nat) (hleftRight : left < right) :
    suzukiDF6D4OddOffDiagonal left right =
      suzukiDF6D4OddTailPrefix suzukiDF6D4CompleteSineTransform left right +
        suzukiDF6D4OddTailRemainder
          suzukiDF6D4CompleteSineTransform left right := by
  rw [suzukiDF6D4OddOffDiagonal_eq_signedNormalizedKernel
    left right hleftRight]
  rw [suzukiDF6D4OddConvolutionKernel_eq_tailPrefix_add_remainder
    (left : Real) (right : Real)
    (suzukiDF6D4CompleteSineTransform left)
    (suzukiDF6D4CompleteSineTransform right)
    (by exact_mod_cast (by omega : right ≠ 0))
    (square_sub_ne_zero_of_nat_lt left right hleftRight)]
  unfold suzukiDF6D4OddTailPrefix suzukiDF6D4OddTailRemainder
  ring

theorem suzukiDF6D4ComparisonOddOffDiagonal_eq_tailPrefix_add_remainder
    (left right : Nat) (hleftPos : 0 < left) (hleftRight : left < right) :
    suzukiDF6D4ComparisonOddOffDiagonal left right =
      suzukiDF6D4OddTailPrefix suzukiDF6D4ComparisonSineTransform left right +
        suzukiDF6D4OddTailRemainder
          suzukiDF6D4ComparisonSineTransform left right := by
  rw [suzukiDF6D4ComparisonOddOffDiagonal_eq_signedNormalizedKernel
    left right hleftPos hleftRight]
  rw [suzukiDF6D4OddConvolutionKernel_eq_tailPrefix_add_remainder
    (left : Real) (right : Real)
    (suzukiDF6D4ComparisonSineTransform left)
    (suzukiDF6D4ComparisonSineTransform right)
    (by exact_mod_cast (by omega : right ≠ 0))
    (square_sub_ne_zero_of_nat_lt left right hleftRight)]
  unfold suzukiDF6D4OddTailPrefix suzukiDF6D4OddTailRemainder
  ring

end

end RiemannHypothesisProject.Experiments.M100
