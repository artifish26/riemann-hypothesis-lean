import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard262Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard262Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard262EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard262OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard262EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard262EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 563) := by
  have h := suzukiDF6D4FixedGridShard262Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard262EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 563)) at h
  exact h

theorem suzukiDF6D4FixedGridShard262EvenFull_eq_live :
    suzukiDF6D4FixedGridShard262EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 563) := by
  have h := suzukiDF6D4FixedGridShard262Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard262EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 563)) at h
  exact h

def suzukiDF6D4FixedGridShard262EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard262EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard262EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard262EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard262EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard262EvenResidualData =
      suzukiDF6D4FixedGridShard262EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard262Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard262EvenResidualData =
    suzukiDF6D4FixedGridShard262EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard262EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard262EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 563 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard262EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 563) := by
    rw [suzukiDF6D4FixedGridShard262EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 563
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard262EvenDotSoundness i
          suzukiDF6D4FixedGridShard262EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 563) := by
    simpa [suzukiDF6D4FixedGridShard262EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard262EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 563) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard262EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 563) := by
    rw [suzukiDF6D4FixedGridShard262EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 563
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard262EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard262EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard262EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard262EvenDotSoundness i
            suzukiDF6D4FixedGridShard262EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard262EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard262OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard262OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 563) := by
  have h := suzukiDF6D4FixedGridShard262Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard262OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 563)) at h
  exact h

theorem suzukiDF6D4FixedGridShard262OddFull_eq_live :
    suzukiDF6D4FixedGridShard262OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 563) := by
  have h := suzukiDF6D4FixedGridShard262Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard262OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 563)) at h
  exact h

def suzukiDF6D4FixedGridShard262OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard262OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard262OddDotSoundness i.val
        suzukiDF6D4FixedGridShard262OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard262OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard262OddResidualData =
      suzukiDF6D4FixedGridShard262OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard262Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard262OddResidualData =
    suzukiDF6D4FixedGridShard262OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard262OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard262OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 563 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard262OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 563) := by
    rw [suzukiDF6D4FixedGridShard262OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 563
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard262OddDotSoundness i
          suzukiDF6D4FixedGridShard262OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 563) := by
    simpa [suzukiDF6D4FixedGridShard262OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard262OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 563) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard262OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 563) := by
    rw [suzukiDF6D4FixedGridShard262OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 563
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard262OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard262OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard262OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard262OddDotSoundness i
            suzukiDF6D4FixedGridShard262OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard262OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
