import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointComparisonEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointConvolutionEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointCompleteSineTransformFullTable

/-!
# Full-range convolution enclosures for M100-DF6D4

This module extends the low-block convolution admission through the frozen
residual cutoff `602`.  It covers both the complete Suzuki transform used by
the low-to-far coupling and the comparison transform used by the far energy
block.  All formulas are the exact ordered-mode product-to-sum identities from
the frozen FT3 and DF1 scripts.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! ## Complete-transform convolution through mode 602 -/

def suzukiDF6D4FullEvenOffDiagonalBracketInterval
    (left right : Nat) : RationalInterval :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  (RationalInterval.scale differenceCoefficient
      ((suzukiDF6D4FullTabulatedCompleteSineTransformInterval right).sub
        (suzukiDF6D4FullTabulatedCompleteSineTransformInterval left))).add
    (RationalInterval.scale totalCoefficient
      ((suzukiDF6D4FullTabulatedCompleteSineTransformInterval left).add
        (suzukiDF6D4FullTabulatedCompleteSineTransformInterval right)))

def suzukiDF6D4FullEvenOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  (suzukiDF6D4EvenConvolutionPrefactorInterval left right).mulLeftNonneg
    (suzukiDF6D4FullEvenOffDiagonalBracketInterval left right)

theorem suzukiDF6D4FullEvenOffDiagonalInterval_contains
    (left right : Nat) (hleftRight : left < right) (hright : right ≤ 602) :
    (suzukiDF6D4FullEvenOffDiagonalInterval left right).Contains
      (suzukiDF6D4EvenOffDiagonal left right) := by
  have hleft : left ≤ 602 := (Nat.le_of_lt hleftRight).trans hright
  have hRightTransform :=
    suzukiDF6D4FullTabulatedCompleteSineTransformInterval_contains right hright
  have hLeftTransform :=
    suzukiDF6D4FullTabulatedCompleteSineTransformInterval_contains left hleft
  have hDifference := RationalInterval.contains_sub hRightTransform hLeftTransform
  have hTotal := RationalInterval.contains_add hLeftTransform hRightTransform
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  have hBracket := RationalInterval.contains_add
    (RationalInterval.contains_scale differenceCoefficient hDifference)
    (RationalInterval.contains_scale totalCoefficient hTotal)
  have hProduct := RationalInterval.contains_mulLeftNonneg
    (suzukiDF6D4EvenConvolutionPrefactorInterval_lower_nonneg left right)
    (suzukiDF6D4EvenConvolutionPrefactorInterval_contains left right)
    hBracket
  unfold suzukiDF6D4FullEvenOffDiagonalInterval
    suzukiDF6D4FullEvenOffDiagonalBracketInterval
    suzukiDF6D4EvenOffDiagonal
  dsimp only [difference, differenceCoefficient, totalCoefficient] at hProduct ⊢
  exact hProduct

def suzukiDF6D4FullOddOffDiagonalBracketInterval
    (left right : Nat) : RationalInterval :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  (RationalInterval.scale differenceCoefficient
      ((suzukiDF6D4FullTabulatedCompleteSineTransformInterval right).sub
        (suzukiDF6D4FullTabulatedCompleteSineTransformInterval left))).add
    (RationalInterval.scale totalCoefficient
      ((suzukiDF6D4FullTabulatedCompleteSineTransformInterval left).add
        (suzukiDF6D4FullTabulatedCompleteSineTransformInterval right)))

def suzukiDF6D4FullOddOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  suzukiDF6D4OddConvolutionPrefactorInterval.mulLeftNonneg
    (suzukiDF6D4FullOddOffDiagonalBracketInterval left right)

theorem suzukiDF6D4FullOddOffDiagonalInterval_contains
    (left right : Nat) (hleftPos : 0 < left)
    (hleftRight : left < right) (hright : right ≤ 602) :
    (suzukiDF6D4FullOddOffDiagonalInterval left right).Contains
      (suzukiDF6D4OddOffDiagonal left right) := by
  have hleft : left ≤ 602 := (Nat.le_of_lt hleftRight).trans hright
  have hRightTransform :=
    suzukiDF6D4FullTabulatedCompleteSineTransformInterval_contains right hright
  have hLeftTransform :=
    suzukiDF6D4FullTabulatedCompleteSineTransformInterval_contains left hleft
  have hDifference := RationalInterval.contains_sub hRightTransform hLeftTransform
  have hTotal := RationalInterval.contains_add hLeftTransform hRightTransform
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  have hBracket := RationalInterval.contains_add
    (RationalInterval.contains_scale differenceCoefficient hDifference)
    (RationalInterval.contains_scale totalCoefficient hTotal)
  have hProduct := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4OddConvolutionPrefactorInterval_lower_nonneg
    suzukiDF6D4OddConvolutionPrefactorInterval_contains hBracket
  unfold suzukiDF6D4FullOddOffDiagonalInterval
    suzukiDF6D4FullOddOffDiagonalBracketInterval suzukiDF6D4OddOffDiagonal
  dsimp only [difference, differenceCoefficient, totalCoefficient] at hProduct ⊢
  exact hProduct

/-! ## Comparison-transform convolution -/

def suzukiDF6D4ComparisonEvenOffDiagonal (left right : Nat) : Real :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  ((1 / 2 : Real) * suzukiDF6D4EvenModeScale left *
      suzukiDF6D4EvenModeScale right * Real.pi⁻¹) *
    (((differenceCoefficient : Rat) : Real) *
        (suzukiDF6D4ComparisonSineTransform right -
          suzukiDF6D4ComparisonSineTransform left) +
      ((totalCoefficient : Rat) : Real) *
        (suzukiDF6D4ComparisonSineTransform left +
          suzukiDF6D4ComparisonSineTransform right))

def suzukiDF6D4ComparisonEvenOffDiagonalBracketInterval
    (left right : Nat) : RationalInterval :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  (RationalInterval.scale differenceCoefficient
      ((suzukiDF6D4ComparisonSineTransformInterval right).sub
        (suzukiDF6D4ComparisonSineTransformInterval left))).add
    (RationalInterval.scale totalCoefficient
      ((suzukiDF6D4ComparisonSineTransformInterval left).add
        (suzukiDF6D4ComparisonSineTransformInterval right)))

def suzukiDF6D4ComparisonEvenOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  (suzukiDF6D4EvenConvolutionPrefactorInterval left right).mulLeftNonneg
    (suzukiDF6D4ComparisonEvenOffDiagonalBracketInterval left right)

theorem suzukiDF6D4ComparisonEvenOffDiagonalInterval_contains
    (left right : Nat) (hleftPos : 0 < left) (hleftRight : left < right) :
    (suzukiDF6D4ComparisonEvenOffDiagonalInterval left right).Contains
      (suzukiDF6D4ComparisonEvenOffDiagonal left right) := by
  have hRightTransform :=
    suzukiDF6D4ComparisonSineTransformInterval_contains right (by omega)
  have hLeftTransform :=
    suzukiDF6D4ComparisonSineTransformInterval_contains left hleftPos
  have hDifference := RationalInterval.contains_sub hRightTransform hLeftTransform
  have hTotal := RationalInterval.contains_add hLeftTransform hRightTransform
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  have hBracket := RationalInterval.contains_add
    (RationalInterval.contains_scale differenceCoefficient hDifference)
    (RationalInterval.contains_scale totalCoefficient hTotal)
  have hProduct := RationalInterval.contains_mulLeftNonneg
    (suzukiDF6D4EvenConvolutionPrefactorInterval_lower_nonneg left right)
    (suzukiDF6D4EvenConvolutionPrefactorInterval_contains left right)
    hBracket
  unfold suzukiDF6D4ComparisonEvenOffDiagonalInterval
    suzukiDF6D4ComparisonEvenOffDiagonalBracketInterval
    suzukiDF6D4ComparisonEvenOffDiagonal
  dsimp only [difference, differenceCoefficient, totalCoefficient] at hProduct ⊢
  exact hProduct

def suzukiDF6D4ComparisonOddOffDiagonal (left right : Nat) : Real :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  ((1 / 2 : Real) * Real.pi⁻¹) *
    (((differenceCoefficient : Rat) : Real) *
        (suzukiDF6D4ComparisonSineTransform right -
          suzukiDF6D4ComparisonSineTransform left) +
      ((totalCoefficient : Rat) : Real) *
        (suzukiDF6D4ComparisonSineTransform left +
          suzukiDF6D4ComparisonSineTransform right))

def suzukiDF6D4ComparisonOddOffDiagonalBracketInterval
    (left right : Nat) : RationalInterval :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  (RationalInterval.scale differenceCoefficient
      ((suzukiDF6D4ComparisonSineTransformInterval right).sub
        (suzukiDF6D4ComparisonSineTransformInterval left))).add
    (RationalInterval.scale totalCoefficient
      ((suzukiDF6D4ComparisonSineTransformInterval left).add
        (suzukiDF6D4ComparisonSineTransformInterval right)))

def suzukiDF6D4ComparisonOddOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  suzukiDF6D4OddConvolutionPrefactorInterval.mulLeftNonneg
    (suzukiDF6D4ComparisonOddOffDiagonalBracketInterval left right)

theorem suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
    (left right : Nat) (hleftPos : 0 < left) (hleftRight : left < right) :
    (suzukiDF6D4ComparisonOddOffDiagonalInterval left right).Contains
      (suzukiDF6D4ComparisonOddOffDiagonal left right) := by
  have hRightTransform :=
    suzukiDF6D4ComparisonSineTransformInterval_contains right (by omega)
  have hLeftTransform :=
    suzukiDF6D4ComparisonSineTransformInterval_contains left hleftPos
  have hDifference := RationalInterval.contains_sub hRightTransform hLeftTransform
  have hTotal := RationalInterval.contains_add hLeftTransform hRightTransform
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  have hBracket := RationalInterval.contains_add
    (RationalInterval.contains_scale differenceCoefficient hDifference)
    (RationalInterval.contains_scale totalCoefficient hTotal)
  have hProduct := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4OddConvolutionPrefactorInterval_lower_nonneg
    suzukiDF6D4OddConvolutionPrefactorInterval_contains hBracket
  unfold suzukiDF6D4ComparisonOddOffDiagonalInterval
    suzukiDF6D4ComparisonOddOffDiagonalBracketInterval
    suzukiDF6D4ComparisonOddOffDiagonal
  dsimp only [difference, differenceCoefficient, totalCoefficient] at hProduct ⊢
  exact hProduct

end

end RiemannHypothesisProject.Experiments.M100
