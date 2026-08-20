import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointCompleteSineTransformTable

/-!
# Endpoint convolution enclosures for M100-DF6D4

This module reconstructs every distinct-mode entry of the frozen even cosine
and odd sine blocks from the admitted complete transforms `J_n`.  The formulas
are the exact product-to-sum identities used by the DF5A/DF6D4 scripts; all
interval operations have rational endpoints.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The parity sign used by the frozen convolution reconstruction. -/
def suzukiDF6D4AlternatingSign (mode : Nat) : Rat :=
  if mode % 2 = 1 then 1 else -1

/-- Cosine-basis normalization.  Only the constant mode has the extra
`1 / sqrt 2` factor. -/
def suzukiDF6D4EvenModeScale (mode : Nat) : Real :=
  if mode = 0 then (Real.sqrt 2)⁻¹ else 1

def suzukiDF6D4EvenModeScaleInterval (mode : Nat) : RationalInterval :=
  if mode = 0 then suzukiDF6D4SqrtTwoInterval.invPos
  else RationalInterval.point 1

theorem suzukiDF6D4EvenModeScaleInterval_lower_nonneg
    (mode : Nat) :
    0 ≤ (suzukiDF6D4EvenModeScaleInterval mode).lower := by
  by_cases hmode : mode = 0
  · simp only [suzukiDF6D4EvenModeScaleInterval, hmode, if_pos]
    norm_num [RationalInterval.invPos, suzukiDF6D4SqrtTwoInterval]
  · simp only [suzukiDF6D4EvenModeScaleInterval, hmode, if_neg]
    norm_num [RationalInterval.point]

theorem suzukiDF6D4EvenModeScaleInterval_contains (mode : Nat) :
    (suzukiDF6D4EvenModeScaleInterval mode).Contains
      (suzukiDF6D4EvenModeScale mode) := by
  by_cases hmode : mode = 0
  · simp only [suzukiDF6D4EvenModeScaleInterval,
      suzukiDF6D4EvenModeScale, hmode, if_pos]
    exact RationalInterval.contains_invPos
      (by norm_num [suzukiDF6D4SqrtTwoInterval])
      suzukiDF6D4SqrtTwoInterval_contains
  · simp only [suzukiDF6D4EvenModeScaleInterval,
      suzukiDF6D4EvenModeScale, hmode, if_neg]
    simpa using RationalInterval.contains_point (1 : Rat)

def suzukiDF6D4PiInverseInterval : RationalInterval :=
  suzukiDF6D4PiInterval.invPos

theorem suzukiDF6D4PiInverseInterval_lower_nonneg :
    0 ≤ suzukiDF6D4PiInverseInterval.lower := by
  norm_num [suzukiDF6D4PiInverseInterval, RationalInterval.invPos,
    suzukiDF6D4PiInterval]

theorem suzukiDF6D4PiInverseInterval_contains :
    suzukiDF6D4PiInverseInterval.Contains Real.pi⁻¹ := by
  exact RationalInterval.contains_invPos
    (by norm_num [suzukiDF6D4PiInterval])
    suzukiDF6D4PiInterval_contains

/-- Positive prefactor `s_left s_right / (2 pi)` for the even block. -/
def suzukiDF6D4EvenConvolutionPrefactorInterval
    (left right : Nat) : RationalInterval :=
  (((RationalInterval.point (1 / 2)).mulNonneg
      (suzukiDF6D4EvenModeScaleInterval left)).mulNonneg
      (suzukiDF6D4EvenModeScaleInterval right)).mulNonneg
    suzukiDF6D4PiInverseInterval

theorem suzukiDF6D4EvenConvolutionPrefactorInterval_lower_nonneg
    (left right : Nat) :
    0 ≤ (suzukiDF6D4EvenConvolutionPrefactorInterval left right).lower := by
  unfold suzukiDF6D4EvenConvolutionPrefactorInterval
    RationalInterval.mulNonneg RationalInterval.point
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num)
      (suzukiDF6D4EvenModeScaleInterval_lower_nonneg left))
      (suzukiDF6D4EvenModeScaleInterval_lower_nonneg right))
    suzukiDF6D4PiInverseInterval_lower_nonneg

theorem suzukiDF6D4EvenConvolutionPrefactorInterval_contains
    (left right : Nat) :
    (suzukiDF6D4EvenConvolutionPrefactorInterval left right).Contains
      ((1 / 2 : Real) * suzukiDF6D4EvenModeScale left *
        suzukiDF6D4EvenModeScale right * Real.pi⁻¹) := by
  have hHalf : (RationalInterval.point (1 / 2)).Contains (1 / 2 : Real) := by
    simpa using RationalInterval.contains_point (1 / 2 : Rat)
  have hFirst := RationalInterval.contains_mulNonneg
    (by norm_num [RationalInterval.point])
    (suzukiDF6D4EvenModeScaleInterval_lower_nonneg left)
    hHalf (suzukiDF6D4EvenModeScaleInterval_contains left)
  have hSecond := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.mulNonneg RationalInterval.point
      exact mul_nonneg (by norm_num)
        (suzukiDF6D4EvenModeScaleInterval_lower_nonneg left))
    (suzukiDF6D4EvenModeScaleInterval_lower_nonneg right)
    hFirst (suzukiDF6D4EvenModeScaleInterval_contains right)
  exact RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.mulNonneg RationalInterval.point
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (suzukiDF6D4EvenModeScaleInterval_lower_nonneg left))
        (suzukiDF6D4EvenModeScaleInterval_lower_nonneg right))
    suzukiDF6D4PiInverseInterval_lower_nonneg hSecond
    suzukiDF6D4PiInverseInterval_contains

/-- Exact even off-diagonal coefficient for ordered distinct modes
`left < right`. -/
def suzukiDF6D4EvenOffDiagonal (left right : Nat) : Real :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  ((1 / 2 : Real) * suzukiDF6D4EvenModeScale left *
      suzukiDF6D4EvenModeScale right * Real.pi⁻¹) *
    (((differenceCoefficient : Rat) : Real) *
        (suzukiDF6D4CompleteSineTransform right -
          suzukiDF6D4CompleteSineTransform left) +
      ((totalCoefficient : Rat) : Real) *
        (suzukiDF6D4CompleteSineTransform left +
          suzukiDF6D4CompleteSineTransform right))

def suzukiDF6D4EvenOffDiagonalBracketInterval
    (left right : Nat) : RationalInterval :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  (RationalInterval.scale differenceCoefficient
      ((suzukiDF6D4TabulatedCompleteSineTransformInterval right).sub
        (suzukiDF6D4TabulatedCompleteSineTransformInterval left))).add
    (RationalInterval.scale totalCoefficient
      ((suzukiDF6D4TabulatedCompleteSineTransformInterval left).add
        (suzukiDF6D4TabulatedCompleteSineTransformInterval right)))

def suzukiDF6D4EvenOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  (suzukiDF6D4EvenConvolutionPrefactorInterval left right).mulLeftNonneg
    (suzukiDF6D4EvenOffDiagonalBracketInterval left right)

theorem suzukiDF6D4EvenOffDiagonalInterval_contains
    (left right : Nat) (hleftRight : left < right) (hright : right ≤ 44) :
    (suzukiDF6D4EvenOffDiagonalInterval left right).Contains
      (suzukiDF6D4EvenOffDiagonal left right) := by
  have hleft : left ≤ 44 := (Nat.le_of_lt hleftRight).trans hright
  have hRightTransform :=
    suzukiDF6D4TabulatedCompleteSineTransformInterval_contains right hright
  have hLeftTransform :=
    suzukiDF6D4TabulatedCompleteSineTransformInterval_contains left hleft
  have hDifference := RationalInterval.contains_sub hRightTransform hLeftTransform
  have hTotal := RationalInterval.contains_add hLeftTransform hRightTransform
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  have hDifferenceTerm := RationalInterval.contains_scale
    differenceCoefficient hDifference
  have hTotalTerm := RationalInterval.contains_scale totalCoefficient hTotal
  have hBracket := RationalInterval.contains_add hDifferenceTerm hTotalTerm
  have hProduct := RationalInterval.contains_mulLeftNonneg
    (suzukiDF6D4EvenConvolutionPrefactorInterval_lower_nonneg left right)
    (suzukiDF6D4EvenConvolutionPrefactorInterval_contains left right)
    hBracket
  unfold suzukiDF6D4EvenOffDiagonalInterval
    suzukiDF6D4EvenOffDiagonalBracketInterval
    suzukiDF6D4EvenOffDiagonal
  dsimp only [difference, differenceCoefficient, totalCoefficient] at hProduct ⊢
  exact hProduct

/-- The odd sine block has no zero-mode normalization. -/
def suzukiDF6D4OddConvolutionPrefactorInterval : RationalInterval :=
  (RationalInterval.point (1 / 2)).mulNonneg
    suzukiDF6D4PiInverseInterval

theorem suzukiDF6D4OddConvolutionPrefactorInterval_lower_nonneg :
    0 ≤ suzukiDF6D4OddConvolutionPrefactorInterval.lower := by
  unfold suzukiDF6D4OddConvolutionPrefactorInterval
    RationalInterval.mulNonneg RationalInterval.point
  exact mul_nonneg (by norm_num)
    suzukiDF6D4PiInverseInterval_lower_nonneg

theorem suzukiDF6D4OddConvolutionPrefactorInterval_contains :
    suzukiDF6D4OddConvolutionPrefactorInterval.Contains
      ((1 / 2 : Real) * Real.pi⁻¹) := by
  exact RationalInterval.contains_mulNonneg
    (by norm_num [RationalInterval.point])
    suzukiDF6D4PiInverseInterval_lower_nonneg
    (by simpa using RationalInterval.contains_point (1 / 2 : Rat))
    suzukiDF6D4PiInverseInterval_contains

/-- Exact odd off-diagonal coefficient for positive ordered modes
`left < right`. -/
def suzukiDF6D4OddOffDiagonal (left right : Nat) : Real :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  ((1 / 2 : Real) * Real.pi⁻¹) *
    (((differenceCoefficient : Rat) : Real) *
        (suzukiDF6D4CompleteSineTransform right -
          suzukiDF6D4CompleteSineTransform left) +
      ((totalCoefficient : Rat) : Real) *
        (suzukiDF6D4CompleteSineTransform left +
          suzukiDF6D4CompleteSineTransform right))

def suzukiDF6D4OddOffDiagonalBracketInterval
    (left right : Nat) : RationalInterval :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  (RationalInterval.scale differenceCoefficient
      ((suzukiDF6D4TabulatedCompleteSineTransformInterval right).sub
        (suzukiDF6D4TabulatedCompleteSineTransformInterval left))).add
    (RationalInterval.scale totalCoefficient
      ((suzukiDF6D4TabulatedCompleteSineTransformInterval left).add
        (suzukiDF6D4TabulatedCompleteSineTransformInterval right)))

def suzukiDF6D4OddOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  suzukiDF6D4OddConvolutionPrefactorInterval.mulLeftNonneg
    (suzukiDF6D4OddOffDiagonalBracketInterval left right)

theorem suzukiDF6D4OddOffDiagonalInterval_contains
    (left right : Nat) (hleftPos : 0 < left)
    (hleftRight : left < right) (hright : right ≤ 44) :
    (suzukiDF6D4OddOffDiagonalInterval left right).Contains
      (suzukiDF6D4OddOffDiagonal left right) := by
  have hleft : left ≤ 44 := (Nat.le_of_lt hleftRight).trans hright
  have hRightTransform :=
    suzukiDF6D4TabulatedCompleteSineTransformInterval_contains right hright
  have hLeftTransform :=
    suzukiDF6D4TabulatedCompleteSineTransformInterval_contains left hleft
  have hDifference := RationalInterval.contains_sub hRightTransform hLeftTransform
  have hTotal := RationalInterval.contains_add hLeftTransform hRightTransform
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  have hDifferenceTerm := RationalInterval.contains_scale
    differenceCoefficient hDifference
  have hTotalTerm := RationalInterval.contains_scale totalCoefficient hTotal
  have hBracket := RationalInterval.contains_add hDifferenceTerm hTotalTerm
  have hProduct := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4OddConvolutionPrefactorInterval_lower_nonneg
    suzukiDF6D4OddConvolutionPrefactorInterval_contains hBracket
  unfold suzukiDF6D4OddOffDiagonalInterval
    suzukiDF6D4OddOffDiagonalBracketInterval suzukiDF6D4OddOffDiagonal
  dsimp only [difference, differenceCoefficient, totalCoefficient] at hProduct ⊢
  exact hProduct

/-- Frozen off-diagonal output grid, eight orders finer than the generated
checker entry intervals. -/
def suzukiDF6D4FrozenEvenOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  RationalInterval.roundOut 10000000000000000
    (suzukiDF6D4EvenOffDiagonalInterval left right)

def suzukiDF6D4FrozenOddOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  RationalInterval.roundOut 10000000000000000
    (suzukiDF6D4OddOffDiagonalInterval left right)

theorem suzukiDF6D4FrozenEvenOffDiagonalInterval_contains
    (left right : Nat) (hleftRight : left < right) (hright : right ≤ 44) :
    (suzukiDF6D4FrozenEvenOffDiagonalInterval left right).Contains
      (suzukiDF6D4EvenOffDiagonal left right) := by
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4EvenOffDiagonalInterval_contains left right
      hleftRight hright)

theorem suzukiDF6D4FrozenOddOffDiagonalInterval_contains
    (left right : Nat) (hleftPos : 0 < left)
    (hleftRight : left < right) (hright : right ≤ 44) :
    (suzukiDF6D4FrozenOddOffDiagonalInterval left right).Contains
      (suzukiDF6D4OddOffDiagonal left right) := by
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4OddOffDiagonalInterval_contains left right hleftPos
      hleftRight hright)

end

end RiemannHypothesisProject.Experiments.M100
