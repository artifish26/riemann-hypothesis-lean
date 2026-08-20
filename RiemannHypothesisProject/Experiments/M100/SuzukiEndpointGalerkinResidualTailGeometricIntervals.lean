import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualTailMatrices

/-!
# Geometric residual-tail interval grid for M100-DF6D4

This module encloses the concrete even and odd order-`n^-11` Galerkin
residual envelopes by exact rational interval arithmetic.  It also packages
the resulting diagonal Gram majorants.  The aggregate Young-split matrices
remain a separate receiving layer.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators
open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## Absolute-value and normalized-envelope intervals -/

def suzukiDF6D4AbsInterval (I : RationalInterval) : RationalInterval :=
  ⟨0, max |I.lower| |I.upper|⟩

theorem suzukiDF6D4AbsInterval_contains
    {I : RationalInterval} {x : Real} (hx : I.Contains x) :
    (suzukiDF6D4AbsInterval I).Contains |x| := by
  unfold suzukiDF6D4AbsInterval RationalInterval.Contains
  simp only [Rat.cast_zero, Rat.cast_max, Rat.cast_abs]
  constructor
  · exact abs_nonneg x
  · by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0]
      exact hx.2.trans ((le_abs_self _).trans (le_max_right _ _))
    · rw [abs_of_nonpos (le_of_not_ge hx0)]
      exact (neg_le_neg hx.1).trans
        ((neg_le_abs _).trans (le_max_left _ _))

def suzukiDF6D4EvenNormalizedGeometricEnvelopeInterval
    (m : Nat) (transformInterval boundInterval : RationalInterval) :
    RationalInterval :=
  RationalInterval.scale
    ((m : Rat) ^ 10 /
      (1 - ((m : Rat) / 601) ^ 2))
    (boundInterval.add
      (RationalInterval.scale ((m : Rat) / 601)
        (suzukiDF6D4AbsInterval transformInterval)))

theorem suzukiDF6D4EvenNormalizedGeometricEnvelopeInterval_contains
    (m : Nat) (transform bound : Real)
    (transformInterval boundInterval : RationalInterval)
    (htransform : transformInterval.Contains transform)
    (hbound : boundInterval.Contains bound) :
    (suzukiDF6D4EvenNormalizedGeometricEnvelopeInterval
      m transformInterval boundInterval).Contains
        (suzukiDF6D4EvenNormalizedGeometricEnvelope m transform bound) := by
  have habs := suzukiDF6D4AbsInterval_contains htransform
  have hscaled := RationalInterval.contains_scale ((m : Rat) / 601) habs
  have hsum := RationalInterval.contains_add hbound hscaled
  have h := RationalInterval.contains_scale
    ((m : Rat) ^ 10 / (1 - ((m : Rat) / 601) ^ 2)) hsum
  unfold suzukiDF6D4EvenNormalizedGeometricEnvelopeInterval
    suzukiDF6D4EvenNormalizedGeometricEnvelope
  convert h using 1 <;> push_cast <;> ring

def suzukiDF6D4OddNormalizedGeometricEnvelopeInterval
    (m : Nat) (transformInterval boundInterval : RationalInterval) :
    RationalInterval :=
  RationalInterval.scale
    ((m : Rat) ^ 10 /
      (1 - ((m : Rat) / 601) ^ 2))
    ((suzukiDF6D4AbsInterval transformInterval).add
      (RationalInterval.scale ((m : Rat) / 601) boundInterval))

theorem suzukiDF6D4OddNormalizedGeometricEnvelopeInterval_contains
    (m : Nat) (transform bound : Real)
    (transformInterval boundInterval : RationalInterval)
    (htransform : transformInterval.Contains transform)
    (hbound : boundInterval.Contains bound) :
    (suzukiDF6D4OddNormalizedGeometricEnvelopeInterval
      m transformInterval boundInterval).Contains
        (suzukiDF6D4OddNormalizedGeometricEnvelope m transform bound) := by
  have habs := suzukiDF6D4AbsInterval_contains htransform
  have hscaled := RationalInterval.contains_scale ((m : Rat) / 601) hbound
  have hsum := RationalInterval.contains_add habs hscaled
  have h := RationalInterval.contains_scale
    ((m : Rat) ^ 10 / (1 - ((m : Rat) / 601) ^ 2)) hsum
  unfold suzukiDF6D4OddNormalizedGeometricEnvelopeInterval
    suzukiDF6D4OddNormalizedGeometricEnvelope
  convert h using 1 <;> push_cast <;> ring

/-! ## Frozen transform-bound intervals -/

def suzukiDF6D4RemainderVariationUpperInterval : RationalInterval :=
  RationalInterval.point (225416424470513 / 500000000000000)

theorem suzukiDF6D4RemainderVariationUpperInterval_contains :
    suzukiDF6D4RemainderVariationUpperInterval.Contains
      suzukiDF6D4RemainderVariationUpper := by
  simpa [suzukiDF6D4RemainderVariationUpperInterval,
    suzukiDF6D4RemainderVariationUpper] using
    RationalInterval.contains_point
      (225416424470513 / 500000000000000 : Rat)

def suzukiDF6D4CompleteTailTransformBoundInterval : RationalInterval :=
  (suzukiDF6D4ComparisonTailTransformBoundInterval.add
    suzukiDF6D4PrimeTailAmplitudeInterval).add
      (RationalInterval.scale (1 / 601)
        (RationalInterval.scale 2
          ((suzukiDF6D4RemainderVariationUpperInterval.mulCentered
            fineAStarInterval).mulCentered suzukiDF6D4PiInverseInterval)))

theorem suzukiDF6D4CompleteTailTransformBoundInterval_contains :
    suzukiDF6D4CompleteTailTransformBoundInterval.Contains
      suzukiDF6D4CompleteTailTransformBound := by
  have hsmoothProduct := RationalInterval.contains_mulCentered
    (RationalInterval.contains_mulCentered
      suzukiDF6D4RemainderVariationUpperInterval_contains
      fineAStarInterval_contains)
    suzukiDF6D4PiInverseInterval_contains
  have hsmooth := RationalInterval.contains_scale (1 / 601)
    (RationalInterval.contains_scale 2 hsmoothProduct)
  have h := RationalInterval.contains_add
    (RationalInterval.contains_add
      suzukiDF6D4ComparisonTailTransformBoundInterval_contains
      suzukiDF6D4PrimeTailAmplitudeInterval_contains)
    hsmooth
  unfold suzukiDF6D4CompleteTailTransformBoundInterval
  unfold suzukiDF6D4ComparisonTailTransformBound
    suzukiDF6D4PrimeTailAmplitude at h
  unfold suzukiDF6D4CompleteTailTransformBound
  convert h using 1 <;> ring

/-! ## Coordinate geometric-envelope intervals -/

def suzukiDF6D4EvenGeometricEnvelopeInterval
    (m : Nat) (transformInterval boundInterval : RationalInterval) :
    RationalInterval :=
  ((suzukiDF6D4AbsInterval (suzukiDF6D4EvenModeScaleInterval m)).mulCentered
      suzukiDF6D4PiInverseInterval).mulCentered
    (suzukiDF6D4EvenNormalizedGeometricEnvelopeInterval
      m transformInterval boundInterval)

theorem suzukiDF6D4EvenGeometricEnvelopeInterval_contains
    (transform : Nat → Real) (transformInterval : Nat → RationalInterval)
    (m : Nat) (bound : Real) (boundInterval : RationalInterval)
    (htransform : (transformInterval m).Contains (transform m))
    (hbound : boundInterval.Contains bound) :
    (suzukiDF6D4EvenGeometricEnvelopeInterval
      m (transformInterval m) boundInterval).Contains
        (suzukiDF6D4EvenGeometricEnvelope transform m bound) := by
  have hscaleAbs := suzukiDF6D4AbsInterval_contains
    (suzukiDF6D4EvenModeScaleInterval_contains m)
  have hprefactor := RationalInterval.contains_mulCentered hscaleAbs
    suzukiDF6D4PiInverseInterval_contains
  have hnormalized :=
    suzukiDF6D4EvenNormalizedGeometricEnvelopeInterval_contains
      m (transform m) bound (transformInterval m) boundInterval
      htransform hbound
  exact RationalInterval.contains_mulCentered hprefactor hnormalized

def suzukiDF6D4OddGeometricEnvelopeInterval
    (m : Nat) (transformInterval boundInterval : RationalInterval) :
    RationalInterval :=
  suzukiDF6D4PiInverseInterval.mulCentered
    (suzukiDF6D4OddNormalizedGeometricEnvelopeInterval
      m transformInterval boundInterval)

theorem suzukiDF6D4OddGeometricEnvelopeInterval_contains
    (transform : Nat → Real) (transformInterval : Nat → RationalInterval)
    (m : Nat) (bound : Real) (boundInterval : RationalInterval)
    (htransform : (transformInterval m).Contains (transform m))
    (hbound : boundInterval.Contains bound) :
    (suzukiDF6D4OddGeometricEnvelopeInterval
      m (transformInterval m) boundInterval).Contains
        (suzukiDF6D4OddGeometricEnvelope transform m bound) := by
  exact RationalInterval.contains_mulCentered
    suzukiDF6D4PiInverseInterval_contains
    (suzukiDF6D4OddNormalizedGeometricEnvelopeInterval_contains
      m (transform m) bound (transformInterval m) boundInterval
      htransform hbound)

def suzukiDF6D4EvenResidualGeometricEnvelopeInterval
    (i : Fin 45) : RationalInterval :=
  (suzukiDF6D4EvenGeometricEnvelopeInterval
    (suzukiDF6D4EvenLowMode i)
    (suzukiDF6D4FullTabulatedCompleteSineTransformInterval
      (suzukiDF6D4EvenLowMode i))
    suzukiDF6D4CompleteTailTransformBoundInterval).add
  (RationalInterval.sum Finset.univ fun k : Fin 256 =>
    RationalInterval.scale |suzukiDF6D4EvenGalerkinApproximant k i|
      (suzukiDF6D4EvenGeometricEnvelopeInterval
        (suzukiDF6D4GalerkinMode k)
        (suzukiDF6D4TabulatedComparisonSineTransformInterval
          (suzukiDF6D4GalerkinMode k))
        suzukiDF6D4ComparisonTailTransformBoundInterval))

theorem suzukiDF6D4EvenResidualGeometricEnvelopeInterval_contains
    (i : Fin 45) :
    (suzukiDF6D4EvenResidualGeometricEnvelopeInterval i).Contains
      (suzukiDF6D4EvenResidualGeometricEnvelope i) := by
  apply RationalInterval.contains_add
  · exact suzukiDF6D4EvenGeometricEnvelopeInterval_contains
      suzukiDF6D4CompleteSineTransform
      suzukiDF6D4FullTabulatedCompleteSineTransformInterval
      (suzukiDF6D4EvenLowMode i)
      suzukiDF6D4CompleteTailTransformBound
      suzukiDF6D4CompleteTailTransformBoundInterval
      (suzukiDF6D4FullTabulatedCompleteSineTransformInterval_contains _
        (by simp [suzukiDF6D4EvenLowMode]; omega))
      suzukiDF6D4CompleteTailTransformBoundInterval_contains
  · exact RationalInterval.contains_sum fun k _ => by
      have hscaled := RationalInterval.contains_scale
        |suzukiDF6D4EvenGalerkinApproximant k i|
        (suzukiDF6D4EvenGeometricEnvelopeInterval_contains
          suzukiDF6D4ComparisonSineTransform
          suzukiDF6D4TabulatedComparisonSineTransformInterval
          (suzukiDF6D4GalerkinMode k)
          suzukiDF6D4ComparisonTailTransformBound
          suzukiDF6D4ComparisonTailTransformBoundInterval
          (suzukiDF6D4TabulatedComparisonSineTransformInterval_contains _
            (by simp [suzukiDF6D4GalerkinMode]; omega)
            (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
          suzukiDF6D4ComparisonTailTransformBoundInterval_contains)
      simpa only [Rat.cast_abs] using hscaled

def suzukiDF6D4OddResidualGeometricEnvelopeInterval
    (i : Fin 44) : RationalInterval :=
  (suzukiDF6D4OddGeometricEnvelopeInterval
    (suzukiDF6D4OddLowMode i)
    (suzukiDF6D4FullTabulatedCompleteSineTransformInterval
      (suzukiDF6D4OddLowMode i))
    suzukiDF6D4CompleteTailTransformBoundInterval).add
  (RationalInterval.sum Finset.univ fun k : Fin 256 =>
    RationalInterval.scale |suzukiDF6D4OddGalerkinApproximant k i|
      (suzukiDF6D4OddGeometricEnvelopeInterval
        (suzukiDF6D4GalerkinMode k)
        (suzukiDF6D4TabulatedComparisonSineTransformInterval
          (suzukiDF6D4GalerkinMode k))
        suzukiDF6D4ComparisonTailTransformBoundInterval))

theorem suzukiDF6D4OddResidualGeometricEnvelopeInterval_contains
    (i : Fin 44) :
    (suzukiDF6D4OddResidualGeometricEnvelopeInterval i).Contains
      (suzukiDF6D4OddResidualGeometricEnvelope i) := by
  apply RationalInterval.contains_add
  · exact suzukiDF6D4OddGeometricEnvelopeInterval_contains
      suzukiDF6D4CompleteSineTransform
      suzukiDF6D4FullTabulatedCompleteSineTransformInterval
      (suzukiDF6D4OddLowMode i)
      suzukiDF6D4CompleteTailTransformBound
      suzukiDF6D4CompleteTailTransformBoundInterval
      (suzukiDF6D4FullTabulatedCompleteSineTransformInterval_contains _
        (by simp [suzukiDF6D4OddLowMode]; omega))
      suzukiDF6D4CompleteTailTransformBoundInterval_contains
  · exact RationalInterval.contains_sum fun k _ => by
      have hscaled := RationalInterval.contains_scale
        |suzukiDF6D4OddGalerkinApproximant k i|
        (suzukiDF6D4OddGeometricEnvelopeInterval_contains
          suzukiDF6D4ComparisonSineTransform
          suzukiDF6D4TabulatedComparisonSineTransformInterval
          (suzukiDF6D4GalerkinMode k)
          suzukiDF6D4ComparisonTailTransformBound
          suzukiDF6D4ComparisonTailTransformBoundInterval
          (suzukiDF6D4TabulatedComparisonSineTransformInterval_contains _
            (by simp [suzukiDF6D4GalerkinMode]; omega)
            (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
          suzukiDF6D4ComparisonTailTransformBoundInterval_contains)
      simpa only [Rat.cast_abs] using hscaled

end

end RiemannHypothesisProject.Experiments.M100
