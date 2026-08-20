import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard123Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard123Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard123EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard123EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 123 k) := by
  have h := suzukiDF6D4FixedGridShard123Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard123EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 123 k)) at h
  exact h

def suzukiDF6D4FixedGridShard123EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard123EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard123EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard123EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard123EvenComparisonData)

theorem suzukiDF6D4FixedGridShard123EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard123EvenSolveData =
      suzukiDF6D4FixedGridShard123EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard123Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard123EvenSolveData =
    suzukiDF6D4FixedGridShard123EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard123EvenCross_eq_live :
    suzukiDF6D4FixedGridShard123EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 123) := by
  have h := suzukiDF6D4FixedGridShard123Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard123EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 123)) at h
  exact h

theorem suzukiDF6D4FixedGridShard123EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard123EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 123 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 123 k) := by
    rw [suzukiDF6D4FixedGridShard123EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 123 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123EvenDotSoundness i
          suzukiDF6D4FixedGridShard123EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 123 k) := by
    simpa [suzukiDF6D4FixedGridShard123EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard123EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 123 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 123) := by
    rw [suzukiDF6D4FixedGridShard123EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 123)
  rw [suzukiDF6D4FixedGridShard123EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard123EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard123EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard123EvenDotSoundness i
            suzukiDF6D4FixedGridShard123EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard123EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard123OddComparison_eq_live :
    suzukiDF6D4FixedGridShard123OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 123 k) := by
  have h := suzukiDF6D4FixedGridShard123Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard123OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 123 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard123OddCross_eq_live :
    suzukiDF6D4FixedGridShard123OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 123) := by
  have h := suzukiDF6D4FixedGridShard123Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard123OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 123)) at h
  exact h

def suzukiDF6D4FixedGridShard123OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard123OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard123OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard123OddDotSoundness i.val
      suzukiDF6D4FixedGridShard123OddComparisonData)

theorem suzukiDF6D4FixedGridShard123OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard123OddSolveData =
      suzukiDF6D4FixedGridShard123OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard123Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard123OddSolveData =
    suzukiDF6D4FixedGridShard123OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard123OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard123OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 123 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 123 k) := by
    rw [suzukiDF6D4FixedGridShard123OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 123 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123OddDotSoundness i
          suzukiDF6D4FixedGridShard123OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 123 k) := by
    simpa [suzukiDF6D4FixedGridShard123OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard123OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 123 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 123) := by
    rw [suzukiDF6D4FixedGridShard123OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 123)
  rw [suzukiDF6D4FixedGridShard123OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard123OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard123OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard123OddDotSoundness i
            suzukiDF6D4FixedGridShard123OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard123OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard123EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard123EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 424) := by
  have h := suzukiDF6D4FixedGridShard123Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard123EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 424)) at h
  exact h

theorem suzukiDF6D4FixedGridShard123EvenFull_eq_live :
    suzukiDF6D4FixedGridShard123EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 424) := by
  have h := suzukiDF6D4FixedGridShard123Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard123EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 424)) at h
  exact h

def suzukiDF6D4FixedGridShard123EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard123EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard123EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard123EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard123EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard123EvenResidualData =
      suzukiDF6D4FixedGridShard123EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard123Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard123EvenResidualData =
    suzukiDF6D4FixedGridShard123EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard123EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard123EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 424 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 424) := by
    rw [suzukiDF6D4FixedGridShard123EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 424
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123EvenDotSoundness i
          suzukiDF6D4FixedGridShard123EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 424) := by
    simpa [suzukiDF6D4FixedGridShard123EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard123EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 424) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 424) := by
    rw [suzukiDF6D4FixedGridShard123EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 424
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard123EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard123EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard123EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard123EvenDotSoundness i
            suzukiDF6D4FixedGridShard123EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard123EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard123OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard123OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 424) := by
  have h := suzukiDF6D4FixedGridShard123Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard123OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 424)) at h
  exact h

theorem suzukiDF6D4FixedGridShard123OddFull_eq_live :
    suzukiDF6D4FixedGridShard123OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 424) := by
  have h := suzukiDF6D4FixedGridShard123Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard123OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 424)) at h
  exact h

def suzukiDF6D4FixedGridShard123OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard123OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard123OddDotSoundness i.val
        suzukiDF6D4FixedGridShard123OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard123OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard123OddResidualData =
      suzukiDF6D4FixedGridShard123OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard123Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard123OddResidualData =
    suzukiDF6D4FixedGridShard123OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard123OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard123OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 424 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 424) := by
    rw [suzukiDF6D4FixedGridShard123OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 424
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123OddDotSoundness i
          suzukiDF6D4FixedGridShard123OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 424) := by
    simpa [suzukiDF6D4FixedGridShard123OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard123OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 424) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard123OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 424) := by
    rw [suzukiDF6D4FixedGridShard123OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 424
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard123OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard123OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard123OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard123OddDotSoundness i
            suzukiDF6D4FixedGridShard123OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard123OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
