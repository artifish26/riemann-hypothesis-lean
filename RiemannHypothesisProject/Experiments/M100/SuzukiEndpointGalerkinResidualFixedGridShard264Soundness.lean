import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard264Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard264Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard264EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard264OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard264EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard264EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 565) := by
  have h := suzukiDF6D4FixedGridShard264Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard264EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 565)) at h
  exact h

theorem suzukiDF6D4FixedGridShard264EvenFull_eq_live :
    suzukiDF6D4FixedGridShard264EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 565) := by
  have h := suzukiDF6D4FixedGridShard264Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard264EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 565)) at h
  exact h

def suzukiDF6D4FixedGridShard264EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard264EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard264EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard264EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard264EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard264EvenResidualData =
      suzukiDF6D4FixedGridShard264EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard264Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard264EvenResidualData =
    suzukiDF6D4FixedGridShard264EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard264EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard264EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 565 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard264EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 565) := by
    rw [suzukiDF6D4FixedGridShard264EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 565
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard264EvenDotSoundness i
          suzukiDF6D4FixedGridShard264EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 565) := by
    simpa [suzukiDF6D4FixedGridShard264EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard264EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 565) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard264EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 565) := by
    rw [suzukiDF6D4FixedGridShard264EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 565
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard264EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard264EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard264EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard264EvenDotSoundness i
            suzukiDF6D4FixedGridShard264EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard264EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard264OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard264OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 565) := by
  have h := suzukiDF6D4FixedGridShard264Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard264OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 565)) at h
  exact h

theorem suzukiDF6D4FixedGridShard264OddFull_eq_live :
    suzukiDF6D4FixedGridShard264OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 565) := by
  have h := suzukiDF6D4FixedGridShard264Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard264OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 565)) at h
  exact h

def suzukiDF6D4FixedGridShard264OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard264OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard264OddDotSoundness i.val
        suzukiDF6D4FixedGridShard264OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard264OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard264OddResidualData =
      suzukiDF6D4FixedGridShard264OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard264Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard264OddResidualData =
    suzukiDF6D4FixedGridShard264OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard264OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard264OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 565 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard264OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 565) := by
    rw [suzukiDF6D4FixedGridShard264OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 565
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard264OddDotSoundness i
          suzukiDF6D4FixedGridShard264OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 565) := by
    simpa [suzukiDF6D4FixedGridShard264OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard264OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 565) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard264OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 565) := by
    rw [suzukiDF6D4FixedGridShard264OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 565
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard264OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard264OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard264OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard264OddDotSoundness i
            suzukiDF6D4FixedGridShard264OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard264OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
