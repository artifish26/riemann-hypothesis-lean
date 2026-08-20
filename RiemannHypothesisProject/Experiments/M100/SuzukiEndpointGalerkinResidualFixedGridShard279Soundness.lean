import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard279Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard279Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard279EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard279OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard279EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard279EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 580) := by
  have h := suzukiDF6D4FixedGridShard279Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard279EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 580)) at h
  exact h

theorem suzukiDF6D4FixedGridShard279EvenFull_eq_live :
    suzukiDF6D4FixedGridShard279EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 580) := by
  have h := suzukiDF6D4FixedGridShard279Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard279EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 580)) at h
  exact h

def suzukiDF6D4FixedGridShard279EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard279EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard279EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard279EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard279EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard279EvenResidualData =
      suzukiDF6D4FixedGridShard279EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard279Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard279EvenResidualData =
    suzukiDF6D4FixedGridShard279EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard279EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard279EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 580 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard279EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 580) := by
    rw [suzukiDF6D4FixedGridShard279EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 580
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard279EvenDotSoundness i
          suzukiDF6D4FixedGridShard279EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 580) := by
    simpa [suzukiDF6D4FixedGridShard279EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard279EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 580) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard279EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 580) := by
    rw [suzukiDF6D4FixedGridShard279EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 580
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard279EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard279EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard279EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard279EvenDotSoundness i
            suzukiDF6D4FixedGridShard279EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard279EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard279OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard279OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 580) := by
  have h := suzukiDF6D4FixedGridShard279Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard279OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 580)) at h
  exact h

theorem suzukiDF6D4FixedGridShard279OddFull_eq_live :
    suzukiDF6D4FixedGridShard279OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 580) := by
  have h := suzukiDF6D4FixedGridShard279Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard279OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 580)) at h
  exact h

def suzukiDF6D4FixedGridShard279OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard279OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard279OddDotSoundness i.val
        suzukiDF6D4FixedGridShard279OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard279OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard279OddResidualData =
      suzukiDF6D4FixedGridShard279OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard279Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard279OddResidualData =
    suzukiDF6D4FixedGridShard279OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard279OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard279OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 580 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard279OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 580) := by
    rw [suzukiDF6D4FixedGridShard279OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 580
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard279OddDotSoundness i
          suzukiDF6D4FixedGridShard279OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 580) := by
    simpa [suzukiDF6D4FixedGridShard279OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard279OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 580) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard279OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 580) := by
    rw [suzukiDF6D4FixedGridShard279OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 580
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard279OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard279OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard279OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard279OddDotSoundness i
            suzukiDF6D4FixedGridShard279OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard279OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
