import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard051Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard051Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard051EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard051EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 51 k) := by
  have h := suzukiDF6D4FixedGridShard051Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard051EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 51 k)) at h
  exact h

def suzukiDF6D4FixedGridShard051EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard051EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard051EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard051EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard051EvenComparisonData)

theorem suzukiDF6D4FixedGridShard051EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard051EvenSolveData =
      suzukiDF6D4FixedGridShard051EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard051Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard051EvenSolveData =
    suzukiDF6D4FixedGridShard051EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard051EvenCross_eq_live :
    suzukiDF6D4FixedGridShard051EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 51) := by
  have h := suzukiDF6D4FixedGridShard051Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard051EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 51)) at h
  exact h

theorem suzukiDF6D4FixedGridShard051EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard051EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 51 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 51 k) := by
    rw [suzukiDF6D4FixedGridShard051EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 51 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051EvenDotSoundness i
          suzukiDF6D4FixedGridShard051EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 51 k) := by
    simpa [suzukiDF6D4FixedGridShard051EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard051EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 51 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 51) := by
    rw [suzukiDF6D4FixedGridShard051EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 51)
  rw [suzukiDF6D4FixedGridShard051EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard051EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard051EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard051EvenDotSoundness i
            suzukiDF6D4FixedGridShard051EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard051EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard051OddComparison_eq_live :
    suzukiDF6D4FixedGridShard051OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 51 k) := by
  have h := suzukiDF6D4FixedGridShard051Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard051OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 51 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard051OddCross_eq_live :
    suzukiDF6D4FixedGridShard051OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 51) := by
  have h := suzukiDF6D4FixedGridShard051Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard051OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 51)) at h
  exact h

def suzukiDF6D4FixedGridShard051OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard051OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard051OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard051OddDotSoundness i.val
      suzukiDF6D4FixedGridShard051OddComparisonData)

theorem suzukiDF6D4FixedGridShard051OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard051OddSolveData =
      suzukiDF6D4FixedGridShard051OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard051Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard051OddSolveData =
    suzukiDF6D4FixedGridShard051OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard051OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard051OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 51 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 51 k) := by
    rw [suzukiDF6D4FixedGridShard051OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 51 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051OddDotSoundness i
          suzukiDF6D4FixedGridShard051OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 51 k) := by
    simpa [suzukiDF6D4FixedGridShard051OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard051OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 51 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 51) := by
    rw [suzukiDF6D4FixedGridShard051OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 51)
  rw [suzukiDF6D4FixedGridShard051OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard051OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard051OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard051OddDotSoundness i
            suzukiDF6D4FixedGridShard051OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard051OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard051EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard051EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 352) := by
  have h := suzukiDF6D4FixedGridShard051Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard051EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 352)) at h
  exact h

theorem suzukiDF6D4FixedGridShard051EvenFull_eq_live :
    suzukiDF6D4FixedGridShard051EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 352) := by
  have h := suzukiDF6D4FixedGridShard051Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard051EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 352)) at h
  exact h

def suzukiDF6D4FixedGridShard051EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard051EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard051EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard051EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard051EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard051EvenResidualData =
      suzukiDF6D4FixedGridShard051EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard051Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard051EvenResidualData =
    suzukiDF6D4FixedGridShard051EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard051EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard051EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 352 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 352) := by
    rw [suzukiDF6D4FixedGridShard051EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 352
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051EvenDotSoundness i
          suzukiDF6D4FixedGridShard051EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 352) := by
    simpa [suzukiDF6D4FixedGridShard051EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard051EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 352) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 352) := by
    rw [suzukiDF6D4FixedGridShard051EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 352
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard051EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard051EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard051EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard051EvenDotSoundness i
            suzukiDF6D4FixedGridShard051EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard051EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard051OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard051OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 352) := by
  have h := suzukiDF6D4FixedGridShard051Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard051OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 352)) at h
  exact h

theorem suzukiDF6D4FixedGridShard051OddFull_eq_live :
    suzukiDF6D4FixedGridShard051OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 352) := by
  have h := suzukiDF6D4FixedGridShard051Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard051OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 352)) at h
  exact h

def suzukiDF6D4FixedGridShard051OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard051OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard051OddDotSoundness i.val
        suzukiDF6D4FixedGridShard051OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard051OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard051OddResidualData =
      suzukiDF6D4FixedGridShard051OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard051Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard051OddResidualData =
    suzukiDF6D4FixedGridShard051OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard051OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard051OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 352 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 352) := by
    rw [suzukiDF6D4FixedGridShard051OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 352
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051OddDotSoundness i
          suzukiDF6D4FixedGridShard051OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 352) := by
    simpa [suzukiDF6D4FixedGridShard051OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard051OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 352) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard051OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 352) := by
    rw [suzukiDF6D4FixedGridShard051OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 352
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard051OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard051OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard051OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard051OddDotSoundness i
            suzukiDF6D4FixedGridShard051OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard051OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
