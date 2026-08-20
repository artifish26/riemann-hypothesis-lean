import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointPrimeTailIntervals
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualTailIntervals

/-!
# Rational matrix enclosures for the M100-DF6D4 analytic residual tail

This module turns the sharp scalar tail sums and the frozen residual-moment
vectors into symmetric real matrices with exact rational entry enclosures.
The matrices are kept separate from the final endpoint checker so every
analytic contribution remains visible.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators
open RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! ## Generic outer-product algebra -/

def suzukiDF6D4OuterMatrix {d : Nat}
    (coefficient : Real) (left right : Fin d → Real) :
    Matrix (Fin d) (Fin d) Real :=
  fun i j => coefficient * left i * right j

def suzukiDF6D4OuterEntryInterval {d : Nat}
    (coefficient : RationalInterval)
    (left right : Fin d → RationalInterval) (i j : Fin d) :
    RationalInterval :=
  coefficient.mulCentered ((left i).mulCentered (right j))

theorem suzukiDF6D4OuterEntryInterval_contains
    {d : Nat} {coefficient : Real} {coefficientInterval : RationalInterval}
    {left right : Fin d → Real}
    {leftInterval rightInterval : Fin d → RationalInterval}
    (hcoefficient : coefficientInterval.Contains coefficient)
    (hleft : ∀ i, (leftInterval i).Contains (left i))
    (hright : ∀ i, (rightInterval i).Contains (right i))
    (i j : Fin d) :
    (suzukiDF6D4OuterEntryInterval coefficientInterval
      leftInterval rightInterval i j).Contains
        (suzukiDF6D4OuterMatrix coefficient left right i j) := by
  simpa only [suzukiDF6D4OuterEntryInterval,
    suzukiDF6D4OuterMatrix, mul_assoc] using
    RationalInterval.contains_mulCentered hcoefficient
      (RationalInterval.contains_mulCentered (hleft i) (hright j))

theorem suzukiDF6D4OuterMatrix_quadratic
    {d : Nat} (coefficient : Real) (left right x : Fin d → Real) :
    dotProduct x
        (Matrix.mulVec (suzukiDF6D4OuterMatrix coefficient left right) x) =
      coefficient * (∑ i, x i * left i) * (∑ i, x i * right i) := by
  unfold dotProduct Matrix.mulVec suzukiDF6D4OuterMatrix
  calc
    (∑ i, x i * ∑ j, coefficient * left i * right j * x j) =
        ∑ i, (coefficient * (x i * left i)) *
          (∑ j, x j * right j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, coefficient * (x i * left i)) *
        (∑ j, x j * right j) := by rw [Finset.sum_mul]
    _ = coefficient * (∑ i, x i * left i) *
        (∑ j, x j * right j) := by
      rw [← Finset.mul_sum]

/-! ## Frozen scalar intervals -/

def suzukiDF6D4PrimeTailAmplitudeInterval : RationalInterval :=
  fineSqrtTwoInterval.mulCentered fineLogTwoInterval

theorem suzukiDF6D4PrimeTailAmplitudeInterval_contains :
    suzukiDF6D4PrimeTailAmplitudeInterval.Contains
      suzukiDF6D4PrimeTailAmplitude := by
  unfold suzukiDF6D4PrimeTailAmplitudeInterval
    suzukiDF6D4PrimeTailAmplitude
  exact RationalInterval.contains_mulCentered
    fineSqrtTwoInterval_contains fineLogTwoInterval_contains

def suzukiDF6D4PiInverseSquareInterval : RationalInterval :=
  suzukiDF6D4PiInverseInterval.mulCentered suzukiDF6D4PiInverseInterval

theorem suzukiDF6D4PiInverseSquareInterval_contains :
    suzukiDF6D4PiInverseSquareInterval.Contains (Real.pi⁻¹ ^ 2) := by
  unfold suzukiDF6D4PiInverseSquareInterval
  simpa [pow_two] using RationalInterval.contains_mulCentered
    suzukiDF6D4PiInverseInterval_contains
    suzukiDF6D4PiInverseInterval_contains

def suzukiDF6D4EvenTailMainFirstCoefficient : Real :=
  Real.pi⁻¹ ^ 2 * (Real.pi ^ 2 / 4) *
    suzukiDF6D4InverseSquareTail 600

def suzukiDF6D4EvenTailMainSecondCoefficient : Real :=
  Real.pi⁻¹ ^ 2 * suzukiDF6D4PrimeTailAmplitude ^ 2 *
    suzukiDF6D4PrimeSineSquareInverseSquareTail

def suzukiDF6D4EvenTailMainCrossCoefficient : Real :=
  Real.pi⁻¹ ^ 2 * (Real.pi * suzukiDF6D4PrimeTailAmplitude / 2) *
    suzukiDF6D4PrimeSineInverseSquareTail

def suzukiDF6D4OddTailMainCoefficient : Real :=
  Real.pi⁻¹ ^ 2 * suzukiDF6D4InverseSquareTail 600

def suzukiDF6D4EvenTailMainFirstCoefficientInterval : RationalInterval :=
  (suzukiDF6D4PiInverseSquareInterval.mulCentered
      (RationalInterval.scale (1 / 4)
        (suzukiDF6D4PiInterval.mulCentered suzukiDF6D4PiInterval))).mulCentered
    suzukiDF6D4FrozenInverseSquareTailInterval

def suzukiDF6D4EvenTailMainSecondCoefficientInterval : RationalInterval :=
  (suzukiDF6D4PiInverseSquareInterval.mulCentered
      (suzukiDF6D4PrimeTailAmplitudeInterval.mulCentered
        suzukiDF6D4PrimeTailAmplitudeInterval)).mulCentered
    suzukiDF6D4FrozenPrimeSineSquareInverseSquareTailInterval

def suzukiDF6D4EvenTailMainCrossCoefficientInterval : RationalInterval :=
  (suzukiDF6D4PiInverseSquareInterval.mulCentered
      (RationalInterval.scale (1 / 2)
        (suzukiDF6D4PiInterval.mulCentered
          suzukiDF6D4PrimeTailAmplitudeInterval))).mulCentered
    suzukiDF6D4FrozenPrimeSineInverseSquareTailInterval

def suzukiDF6D4OddTailMainCoefficientInterval : RationalInterval :=
  suzukiDF6D4PiInverseSquareInterval.mulCentered
    suzukiDF6D4FrozenInverseSquareTailInterval

theorem suzukiDF6D4EvenTailMainFirstCoefficientInterval_contains :
    suzukiDF6D4EvenTailMainFirstCoefficientInterval.Contains
      suzukiDF6D4EvenTailMainFirstCoefficient := by
  have hPiSq := RationalInterval.contains_mulCentered
    suzukiDF6D4PiInterval_contains suzukiDF6D4PiInterval_contains
  have hPiSqOverFour := RationalInterval.contains_scale (1 / 4) hPiSq
  unfold suzukiDF6D4EvenTailMainFirstCoefficientInterval
    suzukiDF6D4EvenTailMainFirstCoefficient
  convert RationalInterval.contains_mulCentered
    (RationalInterval.contains_mulCentered
      suzukiDF6D4PiInverseSquareInterval_contains hPiSqOverFour)
    suzukiDF6D4FrozenInverseSquareTailInterval_contains using 1
  ring

theorem suzukiDF6D4EvenTailMainSecondCoefficientInterval_contains :
    suzukiDF6D4EvenTailMainSecondCoefficientInterval.Contains
      suzukiDF6D4EvenTailMainSecondCoefficient := by
  have hAmplitudeSq := RationalInterval.contains_mulCentered
    suzukiDF6D4PrimeTailAmplitudeInterval_contains
    suzukiDF6D4PrimeTailAmplitudeInterval_contains
  unfold suzukiDF6D4EvenTailMainSecondCoefficientInterval
    suzukiDF6D4EvenTailMainSecondCoefficient
  convert RationalInterval.contains_mulCentered
    (RationalInterval.contains_mulCentered
      suzukiDF6D4PiInverseSquareInterval_contains hAmplitudeSq)
    suzukiDF6D4FrozenPrimeSineSquareInverseSquareTailInterval_contains using 1
  ring

theorem suzukiDF6D4EvenTailMainCrossCoefficientInterval_contains :
    suzukiDF6D4EvenTailMainCrossCoefficientInterval.Contains
      suzukiDF6D4EvenTailMainCrossCoefficient := by
  have hPiAmplitude := RationalInterval.contains_mulCentered
    suzukiDF6D4PiInterval_contains
    suzukiDF6D4PrimeTailAmplitudeInterval_contains
  have hHalf := RationalInterval.contains_scale (1 / 2) hPiAmplitude
  unfold suzukiDF6D4EvenTailMainCrossCoefficientInterval
    suzukiDF6D4EvenTailMainCrossCoefficient
  convert RationalInterval.contains_mulCentered
    (RationalInterval.contains_mulCentered
      suzukiDF6D4PiInverseSquareInterval_contains hHalf)
    suzukiDF6D4FrozenPrimeSineInverseSquareTailInterval_contains using 1
  ring

theorem suzukiDF6D4OddTailMainCoefficientInterval_contains :
    suzukiDF6D4OddTailMainCoefficientInterval.Contains
      suzukiDF6D4OddTailMainCoefficient := by
  exact RationalInterval.contains_mulCentered
    suzukiDF6D4PiInverseSquareInterval_contains
    suzukiDF6D4FrozenInverseSquareTailInterval_contains

/-! ## Structured-tail scalar coefficients -/

def suzukiDF6D4ComparisonTailTransformBoundInterval : RationalInterval :=
  (RationalInterval.scale (1 / 2) suzukiDF6D4PiInterval).add
    (RationalInterval.scale (1 / 601) suzukiDF6D4PiInverseInterval)

theorem suzukiDF6D4ComparisonTailTransformBoundInterval_contains :
    suzukiDF6D4ComparisonTailTransformBoundInterval.Contains
      suzukiDF6D4ComparisonTailTransformBound := by
  have h := RationalInterval.contains_add
    (RationalInterval.contains_scale (1 / 2)
      suzukiDF6D4PiInterval_contains)
    (RationalInterval.contains_scale (1 / 601)
      suzukiDF6D4PiInverseInterval_contains)
  unfold suzukiDF6D4ComparisonTailTransformBoundInterval
    suzukiDF6D4ComparisonTailTransformBound
  convert h using 1
  rw [one_div, mul_inv_rev]
  norm_num
  ring

def suzukiDF6D4SmoothTailCoefficientInterval : RationalInterval :=
  RationalInterval.scale 2
    ((suzukiDF6D4DF0RemainderVariationInterval.mulCentered
      fineAStarInterval).mulCentered suzukiDF6D4PiInverseInterval)

theorem suzukiDF6D4SmoothTailCoefficientInterval_contains :
    suzukiDF6D4SmoothTailCoefficientInterval.Contains
      suzukiDF6D4SmoothTailCoefficient := by
  have hproduct := RationalInterval.contains_mulCentered
    (RationalInterval.contains_mulCentered
      suzukiDF6D4DF0RemainderVariationInterval_contains
      fineAStarInterval_contains)
    suzukiDF6D4PiInverseInterval_contains
  have h := RationalInterval.contains_scale 2 hproduct
  unfold suzukiDF6D4SmoothTailCoefficientInterval
    suzukiDF6D4SmoothTailCoefficient
  convert h using 1
  rw [div_eq_mul_inv]
  ring

def suzukiDF6D4DeltaTailTransformBoundInterval : RationalInterval :=
  suzukiDF6D4PrimeTailAmplitudeInterval.add
    (RationalInterval.scale (1 / 601)
      suzukiDF6D4SmoothTailCoefficientInterval)

theorem suzukiDF6D4DeltaTailTransformBoundInterval_contains :
    suzukiDF6D4DeltaTailTransformBoundInterval.Contains
      suzukiDF6D4DeltaTailTransformBound := by
  have h := RationalInterval.contains_add
    suzukiDF6D4PrimeTailAmplitudeInterval_contains
    (RationalInterval.contains_scale (1 / 601)
      suzukiDF6D4SmoothTailCoefficientInterval_contains)
  unfold suzukiDF6D4DeltaTailTransformBoundInterval
    suzukiDF6D4DeltaTailTransformBound
  convert h using 1
  unfold suzukiDF6D4PrimeTailAmplitude
  rw [div_eq_mul_inv]
  ring

def suzukiDF6D4ComparisonTailBaseInterval : RationalInterval :=
  suzukiDF6D4PiInverseInterval.mulCentered
    suzukiDF6D4ComparisonTailTransformBoundInterval

theorem suzukiDF6D4ComparisonTailBaseInterval_contains :
    suzukiDF6D4ComparisonTailBaseInterval.Contains
      (Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound) := by
  exact RationalInterval.contains_mulCentered
    suzukiDF6D4PiInverseInterval_contains
    suzukiDF6D4ComparisonTailTransformBoundInterval_contains

def suzukiDF6D4DeltaTailBaseInterval : RationalInterval :=
  suzukiDF6D4PiInverseInterval.mulCentered
    suzukiDF6D4DeltaTailTransformBoundInterval

theorem suzukiDF6D4DeltaTailBaseInterval_contains :
    suzukiDF6D4DeltaTailBaseInterval.Contains
      (Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound) := by
  exact RationalInterval.contains_mulCentered
    suzukiDF6D4PiInverseInterval_contains
    suzukiDF6D4DeltaTailTransformBoundInterval_contains

def suzukiDF6D4SmoothErrorTailBaseInterval : RationalInterval :=
  suzukiDF6D4PiInverseInterval.mulCentered
    suzukiDF6D4SmoothTailCoefficientInterval

theorem suzukiDF6D4SmoothErrorTailBaseInterval_contains :
    suzukiDF6D4SmoothErrorTailBaseInterval.Contains
      (Real.pi⁻¹ * suzukiDF6D4SmoothTailCoefficient) := by
  exact RationalInterval.contains_mulCentered
    suzukiDF6D4PiInverseInterval_contains
    suzukiDF6D4SmoothTailCoefficientInterval_contains

def suzukiDF6D4RankOneTailBoundCoefficient
    (base : Real) (power : Nat) : Real :=
  base ^ 2 /
    (((2 * power - 1 : Nat) : Real) *
      (600 : Real) ^ (2 * power - 1))

def suzukiDF6D4RankOneTailBoundCoefficientInterval
    (base : RationalInterval) (power : Nat) : RationalInterval :=
  RationalInterval.scale
    (1 / (((2 * power - 1 : Nat) : Rat) *
      (600 : Rat) ^ (2 * power - 1)))
    (base.mulCentered base)

theorem suzukiDF6D4RankOneTailBoundCoefficientInterval_contains
    {base : Real} {baseInterval : RationalInterval}
    (power : Nat) (hbase : baseInterval.Contains base) :
    (suzukiDF6D4RankOneTailBoundCoefficientInterval
      baseInterval power).Contains
        (suzukiDF6D4RankOneTailBoundCoefficient base power) := by
  have hsq := RationalInterval.contains_mulCentered hbase hbase
  have h := RationalInterval.contains_scale
    (1 / (((2 * power - 1 : Nat) : Rat) *
      (600 : Rat) ^ (2 * power - 1))) hsq
  unfold suzukiDF6D4RankOneTailBoundCoefficientInterval
    suzukiDF6D4RankOneTailBoundCoefficient
  convert h using 1
  norm_num
  push_cast
  ring

def suzukiDF6D4ComparisonRankOneCoefficientInterval
    (power : Nat) : RationalInterval :=
  suzukiDF6D4RankOneTailBoundCoefficientInterval
    suzukiDF6D4ComparisonTailBaseInterval power

theorem suzukiDF6D4ComparisonRankOneCoefficientInterval_contains
    (power : Nat) :
    (suzukiDF6D4ComparisonRankOneCoefficientInterval power).Contains
      (suzukiDF6D4RankOneTailBoundCoefficient
        (Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound) power) := by
  exact suzukiDF6D4RankOneTailBoundCoefficientInterval_contains power
    suzukiDF6D4ComparisonTailBaseInterval_contains

def suzukiDF6D4DeltaRankOneCoefficientInterval
    (power : Nat) : RationalInterval :=
  suzukiDF6D4RankOneTailBoundCoefficientInterval
    suzukiDF6D4DeltaTailBaseInterval power

theorem suzukiDF6D4DeltaRankOneCoefficientInterval_contains
    (power : Nat) :
    (suzukiDF6D4DeltaRankOneCoefficientInterval power).Contains
      (suzukiDF6D4RankOneTailBoundCoefficient
        (Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound) power) := by
  exact suzukiDF6D4RankOneTailBoundCoefficientInterval_contains power
    suzukiDF6D4DeltaTailBaseInterval_contains

def suzukiDF6D4FixedRankOneCoefficientInterval
    (power : Nat) : RationalInterval :=
  suzukiDF6D4RankOneTailBoundCoefficientInterval
    suzukiDF6D4PiInverseInterval power

theorem suzukiDF6D4FixedRankOneCoefficientInterval_contains
    (power : Nat) :
    (suzukiDF6D4FixedRankOneCoefficientInterval power).Contains
      (suzukiDF6D4RankOneTailBoundCoefficient Real.pi⁻¹ power) := by
  exact suzukiDF6D4RankOneTailBoundCoefficientInterval_contains power
    suzukiDF6D4PiInverseInterval_contains

def suzukiDF6D4ComparisonErrorRankOneCoefficientInterval :
    RationalInterval :=
  suzukiDF6D4RankOneTailBoundCoefficientInterval
    suzukiDF6D4PiInverseSquareInterval 2

theorem suzukiDF6D4ComparisonErrorRankOneCoefficientInterval_contains :
    suzukiDF6D4ComparisonErrorRankOneCoefficientInterval.Contains
      (suzukiDF6D4RankOneTailBoundCoefficient (Real.pi⁻¹ ^ 2) 2) := by
  exact suzukiDF6D4RankOneTailBoundCoefficientInterval_contains 2
    suzukiDF6D4PiInverseSquareInterval_contains

def suzukiDF6D4SmoothErrorRankOneCoefficientInterval :
    RationalInterval :=
  suzukiDF6D4RankOneTailBoundCoefficientInterval
    suzukiDF6D4SmoothErrorTailBaseInterval 2

theorem suzukiDF6D4SmoothErrorRankOneCoefficientInterval_contains :
    suzukiDF6D4SmoothErrorRankOneCoefficientInterval.Contains
      (suzukiDF6D4RankOneTailBoundCoefficient
        (Real.pi⁻¹ * suzukiDF6D4SmoothTailCoefficient) 2) := by
  exact suzukiDF6D4RankOneTailBoundCoefficientInterval_contains 2
    suzukiDF6D4SmoothErrorTailBaseInterval_contains

/-! ## Sharp even and odd main matrices -/

def suzukiDF6D4EvenResidualTailMainMatrix : Matrix (Fin 45) (Fin 45) Real :=
  suzukiDF6D4OuterMatrix suzukiDF6D4EvenTailMainFirstCoefficient
      (suzukiDF6D4EvenResidualTailTransformMoment 0)
      (suzukiDF6D4EvenResidualTailTransformMoment 0) +
    suzukiDF6D4OuterMatrix suzukiDF6D4EvenTailMainSecondCoefficient
      (fun i => suzukiDF6D4EvenTailTransformMoment 0
        (suzukiDF6D4EvenLowMode i))
      (fun i => suzukiDF6D4EvenTailTransformMoment 0
        (suzukiDF6D4EvenLowMode i)) +
    suzukiDF6D4OuterMatrix suzukiDF6D4EvenTailMainCrossCoefficient
      (suzukiDF6D4EvenResidualTailTransformMoment 0)
      (fun i => suzukiDF6D4EvenTailTransformMoment 0
        (suzukiDF6D4EvenLowMode i)) +
    suzukiDF6D4OuterMatrix suzukiDF6D4EvenTailMainCrossCoefficient
      (fun i => suzukiDF6D4EvenTailTransformMoment 0
        (suzukiDF6D4EvenLowMode i))
      (suzukiDF6D4EvenResidualTailTransformMoment 0)

def suzukiDF6D4OddResidualTailMainMatrix : Matrix (Fin 44) (Fin 44) Real :=
  suzukiDF6D4OuterMatrix suzukiDF6D4OddTailMainCoefficient
    (suzukiDF6D4OddResidualTailFixedMoment 0)
    (suzukiDF6D4OddResidualTailFixedMoment 0)

def suzukiDF6D4EvenResidualTailMainEntryInterval
    (i j : Fin 45) : RationalInterval :=
  (((suzukiDF6D4OuterEntryInterval
      suzukiDF6D4EvenTailMainFirstCoefficientInterval
      (suzukiDF6D4EvenResidualTailTransformMomentInterval 0)
      (suzukiDF6D4EvenResidualTailTransformMomentInterval 0) i j).add
    (suzukiDF6D4OuterEntryInterval
      suzukiDF6D4EvenTailMainSecondCoefficientInterval
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval 0
        (suzukiDF6D4EvenLowMode k))
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval 0
        (suzukiDF6D4EvenLowMode k)) i j)).add
    (suzukiDF6D4OuterEntryInterval
      suzukiDF6D4EvenTailMainCrossCoefficientInterval
      (suzukiDF6D4EvenResidualTailTransformMomentInterval 0)
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval 0
        (suzukiDF6D4EvenLowMode k)) i j)).add
    (suzukiDF6D4OuterEntryInterval
      suzukiDF6D4EvenTailMainCrossCoefficientInterval
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval 0
        (suzukiDF6D4EvenLowMode k))
      (suzukiDF6D4EvenResidualTailTransformMomentInterval 0) i j)

def suzukiDF6D4OddResidualTailMainEntryInterval
    (i j : Fin 44) : RationalInterval :=
  suzukiDF6D4OuterEntryInterval
    suzukiDF6D4OddTailMainCoefficientInterval
    (suzukiDF6D4OddResidualTailFixedMomentInterval 0)
    (suzukiDF6D4OddResidualTailFixedMomentInterval 0) i j

theorem suzukiDF6D4EvenResidualTailMainEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenResidualTailMainEntryInterval i j).Contains
      (suzukiDF6D4EvenResidualTailMainMatrix i j) := by
  unfold suzukiDF6D4EvenResidualTailMainEntryInterval
    suzukiDF6D4EvenResidualTailMainMatrix
  exact RationalInterval.contains_add
    (RationalInterval.contains_add
      (RationalInterval.contains_add
        (suzukiDF6D4OuterEntryInterval_contains
          suzukiDF6D4EvenTailMainFirstCoefficientInterval_contains
          (suzukiDF6D4EvenResidualTailTransformMomentInterval_contains 0)
          (suzukiDF6D4EvenResidualTailTransformMomentInterval_contains 0) i j)
        (suzukiDF6D4OuterEntryInterval_contains
          suzukiDF6D4EvenTailMainSecondCoefficientInterval_contains
          (fun k => suzukiDF6D4EvenTailTransformMomentInterval_contains 0
            (suzukiDF6D4EvenLowMode k))
          (fun k => suzukiDF6D4EvenTailTransformMomentInterval_contains 0
            (suzukiDF6D4EvenLowMode k)) i j))
      (suzukiDF6D4OuterEntryInterval_contains
        suzukiDF6D4EvenTailMainCrossCoefficientInterval_contains
        (suzukiDF6D4EvenResidualTailTransformMomentInterval_contains 0)
        (fun k => suzukiDF6D4EvenTailTransformMomentInterval_contains 0
          (suzukiDF6D4EvenLowMode k)) i j))
    (suzukiDF6D4OuterEntryInterval_contains
      suzukiDF6D4EvenTailMainCrossCoefficientInterval_contains
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval_contains 0
        (suzukiDF6D4EvenLowMode k))
      (suzukiDF6D4EvenResidualTailTransformMomentInterval_contains 0) i j)

theorem suzukiDF6D4OddResidualTailMainEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddResidualTailMainEntryInterval i j).Contains
      (suzukiDF6D4OddResidualTailMainMatrix i j) := by
  exact suzukiDF6D4OuterEntryInterval_contains
    suzukiDF6D4OddTailMainCoefficientInterval_contains
    (suzukiDF6D4OddResidualTailFixedMomentInterval_contains 0)
    (suzukiDF6D4OddResidualTailFixedMomentInterval_contains 0) i j

theorem suzukiDF6D4EvenResidualTailMainMatrix_quadratic
    (x : Fin 45 → Real) :
    dotProduct x (Matrix.mulVec suzukiDF6D4EvenResidualTailMainMatrix x) =
      suzukiDF6D4EvenResidualTailMainQuadratic x := by
  simp only [suzukiDF6D4EvenResidualTailMainMatrix, Matrix.add_mulVec,
    dotProduct_add]
  rw [suzukiDF6D4OuterMatrix_quadratic,
    suzukiDF6D4OuterMatrix_quadratic,
    suzukiDF6D4OuterMatrix_quadratic,
    suzukiDF6D4OuterMatrix_quadratic]
  unfold suzukiDF6D4EvenResidualTailMainQuadratic
    suzukiDF6D4EvenTailMainFirstCoefficient
    suzukiDF6D4EvenTailMainSecondCoefficient
    suzukiDF6D4EvenTailMainCrossCoefficient
  dsimp only
  ring

theorem suzukiDF6D4OddResidualTailMainMatrix_quadratic
    (x : Fin 44 → Real) :
    dotProduct x (Matrix.mulVec suzukiDF6D4OddResidualTailMainMatrix x) =
      suzukiDF6D4OddResidualTailMainQuadratic x := by
  unfold suzukiDF6D4OddResidualTailMainMatrix
  rw [suzukiDF6D4OuterMatrix_quadratic]
  unfold suzukiDF6D4OddResidualTailMainQuadratic
    suzukiDF6D4OddTailMainCoefficient
  ring

/-! ## Structured contribution matrices -/

def suzukiDF6D4EvenStructuredTailContributionMatrix
    (index : Fin 15) : Matrix (Fin 45) (Fin 45) Real :=
  let order := index.val / 3
  let slot := index.val % 3
  if order = 0 then
    if slot = 0 then
      suzukiDF6D4OuterMatrix
        (suzukiDF6D4RankOneTailBoundCoefficient (Real.pi⁻¹ ^ 2) 2)
        (suzukiDF6D4EvenResidualTailTransformMoment 0)
        (suzukiDF6D4EvenResidualTailTransformMoment 0)
    else if slot = 1 then
      suzukiDF6D4OuterMatrix
        (suzukiDF6D4RankOneTailBoundCoefficient
          (Real.pi⁻¹ * suzukiDF6D4SmoothTailCoefficient) 2)
        (fun i => suzukiDF6D4EvenTailTransformMoment 0
          (suzukiDF6D4EvenLowMode i))
        (fun i => suzukiDF6D4EvenTailTransformMoment 0
          (suzukiDF6D4EvenLowMode i))
    else
      suzukiDF6D4OuterMatrix
        (suzukiDF6D4RankOneTailBoundCoefficient Real.pi⁻¹ 2)
        (suzukiDF6D4EvenResidualTailFixedMoment 0)
        (suzukiDF6D4EvenResidualTailFixedMoment 0)
  else if slot = 0 then
    suzukiDF6D4OuterMatrix
      (suzukiDF6D4RankOneTailBoundCoefficient
        (Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound)
        (2 * order + 1))
      (suzukiDF6D4EvenResidualTailTransformMoment order)
      (suzukiDF6D4EvenResidualTailTransformMoment order)
  else if slot = 1 then
    suzukiDF6D4OuterMatrix
      (suzukiDF6D4RankOneTailBoundCoefficient
        (Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound)
        (2 * order + 1))
      (fun i => suzukiDF6D4EvenTailTransformMoment order
        (suzukiDF6D4EvenLowMode i))
      (fun i => suzukiDF6D4EvenTailTransformMoment order
        (suzukiDF6D4EvenLowMode i))
  else
    suzukiDF6D4OuterMatrix
      (suzukiDF6D4RankOneTailBoundCoefficient Real.pi⁻¹
        (2 * order + 2))
      (suzukiDF6D4EvenResidualTailFixedMoment order)
      (suzukiDF6D4EvenResidualTailFixedMoment order)

def suzukiDF6D4EvenStructuredTailContributionEntryInterval
    (index : Fin 15) (i j : Fin 45) : RationalInterval :=
  let order := index.val / 3
  let slot := index.val % 3
  if order = 0 then
    if slot = 0 then
      suzukiDF6D4OuterEntryInterval
        suzukiDF6D4ComparisonErrorRankOneCoefficientInterval
        (suzukiDF6D4EvenResidualTailTransformMomentInterval 0)
        (suzukiDF6D4EvenResidualTailTransformMomentInterval 0) i j
    else if slot = 1 then
      suzukiDF6D4OuterEntryInterval
        suzukiDF6D4SmoothErrorRankOneCoefficientInterval
        (fun k => suzukiDF6D4EvenTailTransformMomentInterval 0
          (suzukiDF6D4EvenLowMode k))
        (fun k => suzukiDF6D4EvenTailTransformMomentInterval 0
          (suzukiDF6D4EvenLowMode k)) i j
    else
      suzukiDF6D4OuterEntryInterval
        (suzukiDF6D4FixedRankOneCoefficientInterval 2)
        (suzukiDF6D4EvenResidualTailFixedMomentInterval 0)
        (suzukiDF6D4EvenResidualTailFixedMomentInterval 0) i j
  else if slot = 0 then
    suzukiDF6D4OuterEntryInterval
      (suzukiDF6D4ComparisonRankOneCoefficientInterval (2 * order + 1))
      (suzukiDF6D4EvenResidualTailTransformMomentInterval order)
      (suzukiDF6D4EvenResidualTailTransformMomentInterval order) i j
  else if slot = 1 then
    suzukiDF6D4OuterEntryInterval
      (suzukiDF6D4DeltaRankOneCoefficientInterval (2 * order + 1))
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval order
        (suzukiDF6D4EvenLowMode k))
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval order
        (suzukiDF6D4EvenLowMode k)) i j
  else
    suzukiDF6D4OuterEntryInterval
      (suzukiDF6D4FixedRankOneCoefficientInterval (2 * order + 2))
      (suzukiDF6D4EvenResidualTailFixedMomentInterval order)
      (suzukiDF6D4EvenResidualTailFixedMomentInterval order) i j

theorem suzukiDF6D4EvenStructuredTailContributionEntryInterval_contains
    (index : Fin 15) (i j : Fin 45) :
    (suzukiDF6D4EvenStructuredTailContributionEntryInterval index i j).Contains
      (suzukiDF6D4EvenStructuredTailContributionMatrix index i j) := by
  unfold suzukiDF6D4EvenStructuredTailContributionEntryInterval
    suzukiDF6D4EvenStructuredTailContributionMatrix
  dsimp only
  split_ifs
  · exact suzukiDF6D4OuterEntryInterval_contains
      suzukiDF6D4ComparisonErrorRankOneCoefficientInterval_contains
      (suzukiDF6D4EvenResidualTailTransformMomentInterval_contains 0)
      (suzukiDF6D4EvenResidualTailTransformMomentInterval_contains 0) i j
  · exact suzukiDF6D4OuterEntryInterval_contains
      suzukiDF6D4SmoothErrorRankOneCoefficientInterval_contains
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval_contains 0
        (suzukiDF6D4EvenLowMode k))
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval_contains 0
        (suzukiDF6D4EvenLowMode k)) i j
  · exact suzukiDF6D4OuterEntryInterval_contains
      (suzukiDF6D4FixedRankOneCoefficientInterval_contains 2)
      (suzukiDF6D4EvenResidualTailFixedMomentInterval_contains 0)
      (suzukiDF6D4EvenResidualTailFixedMomentInterval_contains 0) i j
  · exact suzukiDF6D4OuterEntryInterval_contains
      (suzukiDF6D4ComparisonRankOneCoefficientInterval_contains _)
      (suzukiDF6D4EvenResidualTailTransformMomentInterval_contains _)
      (suzukiDF6D4EvenResidualTailTransformMomentInterval_contains _) i j
  · exact suzukiDF6D4OuterEntryInterval_contains
      (suzukiDF6D4DeltaRankOneCoefficientInterval_contains _)
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval_contains _
        (suzukiDF6D4EvenLowMode k))
      (fun k => suzukiDF6D4EvenTailTransformMomentInterval_contains _
        (suzukiDF6D4EvenLowMode k)) i j
  · exact suzukiDF6D4OuterEntryInterval_contains
      (suzukiDF6D4FixedRankOneCoefficientInterval_contains _)
      (suzukiDF6D4EvenResidualTailFixedMomentInterval_contains _)
      (suzukiDF6D4EvenResidualTailFixedMomentInterval_contains _) i j

theorem suzukiDF6D4EvenStructuredTailContributionMatrix_quadratic
    (index : Fin 15) (x : Fin 45 → Real) :
    dotProduct x
        (Matrix.mulVec (suzukiDF6D4EvenStructuredTailContributionMatrix index) x) =
      suzukiDF6D4EvenStructuredTailContributionBound index x := by
  unfold suzukiDF6D4EvenStructuredTailContributionMatrix
    suzukiDF6D4EvenStructuredTailContributionBound
  dsimp only
  split_ifs <;>
    rw [suzukiDF6D4OuterMatrix_quadratic] <;>
    simp only [suzukiDF6D4RankOneTailBoundCoefficient,
      suzukiDF6D4TailComparisonRankOneBound,
      suzukiDF6D4TailDeltaRankOneBound,
      suzukiDF6D4TailFixedRankOneBound,
      suzukiDF6D4TailComparisonErrorRankOneBound,
      suzukiDF6D4TailSmoothErrorRankOneBound] <;>
    ring

def suzukiDF6D4OddStructuredTailContributionMatrix
    (index : Fin 14) : Matrix (Fin 44) (Fin 44) Real :=
  if index.val = 0 then
    suzukiDF6D4OuterMatrix
      (suzukiDF6D4RankOneTailBoundCoefficient
        (Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound) 2)
      (suzukiDF6D4OddResidualTailTransformMoment 0)
      (suzukiDF6D4OddResidualTailTransformMoment 0)
  else if index.val = 1 then
    suzukiDF6D4OuterMatrix
      (suzukiDF6D4RankOneTailBoundCoefficient
        (Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound) 2)
      (fun i => suzukiDF6D4OddTailTransformMoment 0
        (suzukiDF6D4OddLowMode i))
      (fun i => suzukiDF6D4OddTailTransformMoment 0
        (suzukiDF6D4OddLowMode i))
  else
    let order := 1 + (index.val - 2) / 3
    let slot := (index.val - 2) % 3
    if slot = 0 then
      suzukiDF6D4OuterMatrix
        (suzukiDF6D4RankOneTailBoundCoefficient
          (Real.pi⁻¹ * suzukiDF6D4ComparisonTailTransformBound)
          (2 * order + 2))
        (suzukiDF6D4OddResidualTailTransformMoment order)
        (suzukiDF6D4OddResidualTailTransformMoment order)
    else if slot = 1 then
      suzukiDF6D4OuterMatrix
        (suzukiDF6D4RankOneTailBoundCoefficient
          (Real.pi⁻¹ * suzukiDF6D4DeltaTailTransformBound)
          (2 * order + 2))
        (fun i => suzukiDF6D4OddTailTransformMoment order
          (suzukiDF6D4OddLowMode i))
        (fun i => suzukiDF6D4OddTailTransformMoment order
          (suzukiDF6D4OddLowMode i))
    else
      suzukiDF6D4OuterMatrix
        (suzukiDF6D4RankOneTailBoundCoefficient Real.pi⁻¹
          (2 * order + 1))
        (suzukiDF6D4OddResidualTailFixedMoment order)
        (suzukiDF6D4OddResidualTailFixedMoment order)

def suzukiDF6D4OddStructuredTailContributionEntryInterval
    (index : Fin 14) (i j : Fin 44) : RationalInterval :=
  if index.val = 0 then
    suzukiDF6D4OuterEntryInterval
      (suzukiDF6D4ComparisonRankOneCoefficientInterval 2)
      (suzukiDF6D4OddResidualTailTransformMomentInterval 0)
      (suzukiDF6D4OddResidualTailTransformMomentInterval 0) i j
  else if index.val = 1 then
    suzukiDF6D4OuterEntryInterval
      (suzukiDF6D4DeltaRankOneCoefficientInterval 2)
      (fun k => suzukiDF6D4OddTailTransformMomentInterval 0
        (suzukiDF6D4OddLowMode k))
      (fun k => suzukiDF6D4OddTailTransformMomentInterval 0
        (suzukiDF6D4OddLowMode k)) i j
  else
    let order := 1 + (index.val - 2) / 3
    let slot := (index.val - 2) % 3
    if slot = 0 then
      suzukiDF6D4OuterEntryInterval
        (suzukiDF6D4ComparisonRankOneCoefficientInterval (2 * order + 2))
        (suzukiDF6D4OddResidualTailTransformMomentInterval order)
        (suzukiDF6D4OddResidualTailTransformMomentInterval order) i j
    else if slot = 1 then
      suzukiDF6D4OuterEntryInterval
        (suzukiDF6D4DeltaRankOneCoefficientInterval (2 * order + 2))
        (fun k => suzukiDF6D4OddTailTransformMomentInterval order
          (suzukiDF6D4OddLowMode k))
        (fun k => suzukiDF6D4OddTailTransformMomentInterval order
          (suzukiDF6D4OddLowMode k)) i j
    else
      suzukiDF6D4OuterEntryInterval
        (suzukiDF6D4FixedRankOneCoefficientInterval (2 * order + 1))
        (suzukiDF6D4OddResidualTailFixedMomentInterval order)
        (suzukiDF6D4OddResidualTailFixedMomentInterval order) i j

theorem suzukiDF6D4OddStructuredTailContributionEntryInterval_contains
    (index : Fin 14) (i j : Fin 44) :
    (suzukiDF6D4OddStructuredTailContributionEntryInterval index i j).Contains
      (suzukiDF6D4OddStructuredTailContributionMatrix index i j) := by
  unfold suzukiDF6D4OddStructuredTailContributionEntryInterval
    suzukiDF6D4OddStructuredTailContributionMatrix
  dsimp only
  split_ifs
  · exact suzukiDF6D4OuterEntryInterval_contains
      (suzukiDF6D4ComparisonRankOneCoefficientInterval_contains 2)
      (suzukiDF6D4OddResidualTailTransformMomentInterval_contains 0)
      (suzukiDF6D4OddResidualTailTransformMomentInterval_contains 0) i j
  · exact suzukiDF6D4OuterEntryInterval_contains
      (suzukiDF6D4DeltaRankOneCoefficientInterval_contains 2)
      (fun k => suzukiDF6D4OddTailTransformMomentInterval_contains 0
        (suzukiDF6D4OddLowMode k))
      (fun k => suzukiDF6D4OddTailTransformMomentInterval_contains 0
        (suzukiDF6D4OddLowMode k)) i j
  · exact suzukiDF6D4OuterEntryInterval_contains
      (suzukiDF6D4ComparisonRankOneCoefficientInterval_contains _)
      (suzukiDF6D4OddResidualTailTransformMomentInterval_contains _)
      (suzukiDF6D4OddResidualTailTransformMomentInterval_contains _) i j
  · exact suzukiDF6D4OuterEntryInterval_contains
      (suzukiDF6D4DeltaRankOneCoefficientInterval_contains _)
      (fun k => suzukiDF6D4OddTailTransformMomentInterval_contains _
        (suzukiDF6D4OddLowMode k))
      (fun k => suzukiDF6D4OddTailTransformMomentInterval_contains _
        (suzukiDF6D4OddLowMode k)) i j
  · exact suzukiDF6D4OuterEntryInterval_contains
      (suzukiDF6D4FixedRankOneCoefficientInterval_contains _)
      (suzukiDF6D4OddResidualTailFixedMomentInterval_contains _)
      (suzukiDF6D4OddResidualTailFixedMomentInterval_contains _) i j

theorem suzukiDF6D4OddStructuredTailContributionMatrix_quadratic
    (index : Fin 14) (x : Fin 44 → Real) :
    dotProduct x
        (Matrix.mulVec (suzukiDF6D4OddStructuredTailContributionMatrix index) x) =
      suzukiDF6D4OddStructuredTailContributionBound index x := by
  unfold suzukiDF6D4OddStructuredTailContributionMatrix
    suzukiDF6D4OddStructuredTailContributionBound
  dsimp only
  split_ifs <;>
    rw [suzukiDF6D4OuterMatrix_quadratic] <;>
    simp only [suzukiDF6D4RankOneTailBoundCoefficient,
      suzukiDF6D4TailComparisonRankOneBound,
      suzukiDF6D4TailDeltaRankOneBound,
      suzukiDF6D4TailFixedRankOneBound] <;>
    ring

end

end RiemannHypothesisProject.Experiments.M100
