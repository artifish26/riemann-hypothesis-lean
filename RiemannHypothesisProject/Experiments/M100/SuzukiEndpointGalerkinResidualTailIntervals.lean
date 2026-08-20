import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualTailExpansion
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointCompleteSineTransformFullTable
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointComparisonTable

/-!
# Rational residual-moment intervals for M100-DF6D4

The structured analytic tail is controlled by four families of finite row
vectors: transform and fixed moments in each parity.  This module evaluates
those vectors with exact rational interval arithmetic from the frozen
Galerkin approximants and the already proved complete/comparison transform
tables.  No numerical inverse or floating-point conclusion is imported.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators
open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## Coordinate moment intervals -/

def suzukiDF6D4EvenTailTransformMomentInterval
    (order mode : Nat) : RationalInterval :=
  RationalInterval.scale
    (suzukiDF6D4AlternatingSign mode * (mode : Rat) ^ (2 * order))
    (suzukiDF6D4EvenModeScaleInterval mode)

theorem suzukiDF6D4EvenTailTransformMomentInterval_contains
    (order mode : Nat) :
    (suzukiDF6D4EvenTailTransformMomentInterval order mode).Contains
      (suzukiDF6D4EvenTailTransformMoment order mode) := by
  have h := RationalInterval.contains_scale
    (suzukiDF6D4AlternatingSign mode * (mode : Rat) ^ (2 * order))
    (suzukiDF6D4EvenModeScaleInterval_contains mode)
  unfold suzukiDF6D4EvenTailTransformMomentInterval
    suzukiDF6D4EvenTailTransformMoment
  convert h using 1 <;> push_cast <;> ring

def suzukiDF6D4EvenTailFixedMomentInterval
    (transformInterval : Nat → RationalInterval)
    (order mode : Nat) : RationalInterval :=
  RationalInterval.scale
    (suzukiDF6D4AlternatingSign mode * (mode : Rat) ^ (2 * order + 1))
    ((suzukiDF6D4EvenModeScaleInterval mode).mulCentered
      (transformInterval mode))

theorem suzukiDF6D4EvenTailFixedMomentInterval_contains
    (transform : Nat → Real) (transformInterval : Nat → RationalInterval)
    (order mode : Nat)
    (htransform : (transformInterval mode).Contains (transform mode)) :
    (suzukiDF6D4EvenTailFixedMomentInterval
      transformInterval order mode).Contains
        (suzukiDF6D4EvenTailFixedMoment transform order mode) := by
  have hproduct := RationalInterval.contains_mulCentered
    (suzukiDF6D4EvenModeScaleInterval_contains mode) htransform
  have h := RationalInterval.contains_scale
    (suzukiDF6D4AlternatingSign mode * (mode : Rat) ^ (2 * order + 1))
    hproduct
  unfold suzukiDF6D4EvenTailFixedMomentInterval
    suzukiDF6D4EvenTailFixedMoment
  convert h using 1 <;> push_cast <;> ring

def suzukiDF6D4OddTailTransformMomentInterval
    (order mode : Nat) : RationalInterval :=
  RationalInterval.point
    (suzukiDF6D4AlternatingSign mode * (mode : Rat) ^ (2 * order + 1))

theorem suzukiDF6D4OddTailTransformMomentInterval_contains
    (order mode : Nat) :
    (suzukiDF6D4OddTailTransformMomentInterval order mode).Contains
      (suzukiDF6D4OddTailTransformMoment order mode) := by
  have h := RationalInterval.contains_point
    (suzukiDF6D4AlternatingSign mode * (mode : Rat) ^ (2 * order + 1))
  unfold suzukiDF6D4OddTailTransformMomentInterval
    suzukiDF6D4OddTailTransformMoment
  convert h using 1 <;> push_cast <;> ring

def suzukiDF6D4OddTailFixedMomentInterval
    (transformInterval : Nat → RationalInterval)
    (order mode : Nat) : RationalInterval :=
  RationalInterval.scale
    (suzukiDF6D4AlternatingSign mode * (mode : Rat) ^ (2 * order))
    (transformInterval mode)

theorem suzukiDF6D4OddTailFixedMomentInterval_contains
    (transform : Nat → Real) (transformInterval : Nat → RationalInterval)
    (order mode : Nat)
    (htransform : (transformInterval mode).Contains (transform mode)) :
    (suzukiDF6D4OddTailFixedMomentInterval
      transformInterval order mode).Contains
        (suzukiDF6D4OddTailFixedMoment transform order mode) := by
  have h := RationalInterval.contains_scale
    (suzukiDF6D4AlternatingSign mode * (mode : Rat) ^ (2 * order))
    htransform
  unfold suzukiDF6D4OddTailFixedMomentInterval
    suzukiDF6D4OddTailFixedMoment
  convert h using 1 <;> push_cast <;> ring

/-! ## Galerkin residual moment intervals -/

def suzukiDF6D4EvenResidualTailTransformMomentInterval
    (order : Nat) (i : Fin 45) : RationalInterval :=
  (suzukiDF6D4EvenTailTransformMomentInterval order
      (suzukiDF6D4EvenLowMode i)).sub
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k i)
        (suzukiDF6D4EvenTailTransformMomentInterval order
          (suzukiDF6D4GalerkinMode k)))

theorem suzukiDF6D4EvenResidualTailTransformMomentInterval_contains
    (order : Nat) (i : Fin 45) :
    (suzukiDF6D4EvenResidualTailTransformMomentInterval order i).Contains
      (suzukiDF6D4EvenResidualTailTransformMoment order i) := by
  exact RationalInterval.contains_sub
    (suzukiDF6D4EvenTailTransformMomentInterval_contains _ _)
    (RationalInterval.contains_sum fun k _ =>
      RationalInterval.contains_scale _
        (suzukiDF6D4EvenTailTransformMomentInterval_contains _ _))

def suzukiDF6D4EvenResidualTailFixedMomentInterval
    (order : Nat) (i : Fin 45) : RationalInterval :=
  (suzukiDF6D4EvenTailFixedMomentInterval
      suzukiDF6D4FullTabulatedCompleteSineTransformInterval order
      (suzukiDF6D4EvenLowMode i)).sub
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k i)
        (suzukiDF6D4EvenTailFixedMomentInterval
          suzukiDF6D4TabulatedComparisonSineTransformInterval order
          (suzukiDF6D4GalerkinMode k)))

theorem suzukiDF6D4EvenResidualTailFixedMomentInterval_contains
    (order : Nat) (i : Fin 45) :
    (suzukiDF6D4EvenResidualTailFixedMomentInterval order i).Contains
      (suzukiDF6D4EvenResidualTailFixedMoment order i) := by
  apply RationalInterval.contains_sub
  · exact suzukiDF6D4EvenTailFixedMomentInterval_contains
      suzukiDF6D4CompleteSineTransform
      suzukiDF6D4FullTabulatedCompleteSineTransformInterval _ _
      (suzukiDF6D4FullTabulatedCompleteSineTransformInterval_contains _
        (by simp [suzukiDF6D4EvenLowMode]; omega))
  · exact RationalInterval.contains_sum fun k _ =>
      RationalInterval.contains_scale _
        (suzukiDF6D4EvenTailFixedMomentInterval_contains
          suzukiDF6D4ComparisonSineTransform
          suzukiDF6D4TabulatedComparisonSineTransformInterval _ _
          (suzukiDF6D4TabulatedComparisonSineTransformInterval_contains _
            (by simp [suzukiDF6D4GalerkinMode]; omega)
            (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)))

def suzukiDF6D4OddResidualTailTransformMomentInterval
    (order : Nat) (i : Fin 44) : RationalInterval :=
  (suzukiDF6D4OddTailTransformMomentInterval order
      (suzukiDF6D4OddLowMode i)).sub
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k i)
        (suzukiDF6D4OddTailTransformMomentInterval order
          (suzukiDF6D4GalerkinMode k)))

theorem suzukiDF6D4OddResidualTailTransformMomentInterval_contains
    (order : Nat) (i : Fin 44) :
    (suzukiDF6D4OddResidualTailTransformMomentInterval order i).Contains
      (suzukiDF6D4OddResidualTailTransformMoment order i) := by
  exact RationalInterval.contains_sub
    (suzukiDF6D4OddTailTransformMomentInterval_contains _ _)
    (RationalInterval.contains_sum fun k _ =>
      RationalInterval.contains_scale _
        (suzukiDF6D4OddTailTransformMomentInterval_contains _ _))

def suzukiDF6D4OddResidualTailFixedMomentInterval
    (order : Nat) (i : Fin 44) : RationalInterval :=
  (suzukiDF6D4OddTailFixedMomentInterval
      suzukiDF6D4FullTabulatedCompleteSineTransformInterval order
      (suzukiDF6D4OddLowMode i)).sub
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k i)
        (suzukiDF6D4OddTailFixedMomentInterval
          suzukiDF6D4TabulatedComparisonSineTransformInterval order
          (suzukiDF6D4GalerkinMode k)))

theorem suzukiDF6D4OddResidualTailFixedMomentInterval_contains
    (order : Nat) (i : Fin 44) :
    (suzukiDF6D4OddResidualTailFixedMomentInterval order i).Contains
      (suzukiDF6D4OddResidualTailFixedMoment order i) := by
  apply RationalInterval.contains_sub
  · exact suzukiDF6D4OddTailFixedMomentInterval_contains
      suzukiDF6D4CompleteSineTransform
      suzukiDF6D4FullTabulatedCompleteSineTransformInterval _ _
      (suzukiDF6D4FullTabulatedCompleteSineTransformInterval_contains _
        (by simp [suzukiDF6D4OddLowMode]; omega))
  · exact RationalInterval.contains_sum fun k _ =>
      RationalInterval.contains_scale _
        (suzukiDF6D4OddTailFixedMomentInterval_contains
          suzukiDF6D4ComparisonSineTransform
          suzukiDF6D4TabulatedComparisonSineTransformInterval _ _
          (suzukiDF6D4TabulatedComparisonSineTransformInterval_contains _
            (by simp [suzukiDF6D4GalerkinMode]; omega)
            (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)))

end

end RiemannHypothesisProject.Experiments.M100
