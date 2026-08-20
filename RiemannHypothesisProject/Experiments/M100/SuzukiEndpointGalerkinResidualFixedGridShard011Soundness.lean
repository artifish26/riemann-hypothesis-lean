import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard011Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard011Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard011EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard011EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 11 k) := by
  have h := suzukiDF6D4FixedGridShard011Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard011EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 11 k)) at h
  exact h

def suzukiDF6D4FixedGridShard011EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard011EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard011EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard011EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard011EvenComparisonData)

theorem suzukiDF6D4FixedGridShard011EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard011EvenSolveData =
      suzukiDF6D4FixedGridShard011EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard011Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard011EvenSolveData =
    suzukiDF6D4FixedGridShard011EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard011EvenCross_eq_live :
    suzukiDF6D4FixedGridShard011EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 11) := by
  have h := suzukiDF6D4FixedGridShard011Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard011EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 11)) at h
  exact h

theorem suzukiDF6D4FixedGridShard011EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard011EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 11 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 11 k) := by
    rw [suzukiDF6D4FixedGridShard011EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 11 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011EvenDotSoundness i
          suzukiDF6D4FixedGridShard011EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 11 k) := by
    simpa [suzukiDF6D4FixedGridShard011EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard011EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 11 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 11) := by
    rw [suzukiDF6D4FixedGridShard011EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 11)
  rw [suzukiDF6D4FixedGridShard011EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard011EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard011EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard011EvenDotSoundness i
            suzukiDF6D4FixedGridShard011EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard011EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard011OddComparison_eq_live :
    suzukiDF6D4FixedGridShard011OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 11 k) := by
  have h := suzukiDF6D4FixedGridShard011Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard011OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 11 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard011OddCross_eq_live :
    suzukiDF6D4FixedGridShard011OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 11) := by
  have h := suzukiDF6D4FixedGridShard011Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard011OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 11)) at h
  exact h

def suzukiDF6D4FixedGridShard011OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard011OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard011OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard011OddDotSoundness i.val
      suzukiDF6D4FixedGridShard011OddComparisonData)

theorem suzukiDF6D4FixedGridShard011OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard011OddSolveData =
      suzukiDF6D4FixedGridShard011OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard011Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard011OddSolveData =
    suzukiDF6D4FixedGridShard011OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard011OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard011OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 11 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 11 k) := by
    rw [suzukiDF6D4FixedGridShard011OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 11 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011OddDotSoundness i
          suzukiDF6D4FixedGridShard011OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 11 k) := by
    simpa [suzukiDF6D4FixedGridShard011OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard011OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 11 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 11) := by
    rw [suzukiDF6D4FixedGridShard011OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 11)
  rw [suzukiDF6D4FixedGridShard011OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard011OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard011OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard011OddDotSoundness i
            suzukiDF6D4FixedGridShard011OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard011OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard011EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard011EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 312) := by
  have h := suzukiDF6D4FixedGridShard011Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard011EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 312)) at h
  exact h

theorem suzukiDF6D4FixedGridShard011EvenFull_eq_live :
    suzukiDF6D4FixedGridShard011EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 312) := by
  have h := suzukiDF6D4FixedGridShard011Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard011EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 312)) at h
  exact h

def suzukiDF6D4FixedGridShard011EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard011EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard011EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard011EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard011EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard011EvenResidualData =
      suzukiDF6D4FixedGridShard011EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard011Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard011EvenResidualData =
    suzukiDF6D4FixedGridShard011EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard011EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard011EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 312 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 312) := by
    rw [suzukiDF6D4FixedGridShard011EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 312
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011EvenDotSoundness i
          suzukiDF6D4FixedGridShard011EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 312) := by
    simpa [suzukiDF6D4FixedGridShard011EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard011EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 312) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 312) := by
    rw [suzukiDF6D4FixedGridShard011EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 312
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard011EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard011EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard011EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard011EvenDotSoundness i
            suzukiDF6D4FixedGridShard011EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard011EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard011OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard011OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 312) := by
  have h := suzukiDF6D4FixedGridShard011Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard011OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 312)) at h
  exact h

theorem suzukiDF6D4FixedGridShard011OddFull_eq_live :
    suzukiDF6D4FixedGridShard011OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 312) := by
  have h := suzukiDF6D4FixedGridShard011Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard011OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 312)) at h
  exact h

def suzukiDF6D4FixedGridShard011OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard011OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard011OddDotSoundness i.val
        suzukiDF6D4FixedGridShard011OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard011OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard011OddResidualData =
      suzukiDF6D4FixedGridShard011OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard011Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard011OddResidualData =
    suzukiDF6D4FixedGridShard011OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard011OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard011OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 312 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 312) := by
    rw [suzukiDF6D4FixedGridShard011OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 312
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011OddDotSoundness i
          suzukiDF6D4FixedGridShard011OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 312) := by
    simpa [suzukiDF6D4FixedGridShard011OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard011OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 312) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard011OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 312) := by
    rw [suzukiDF6D4FixedGridShard011OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 312
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard011OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard011OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard011OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard011OddDotSoundness i
            suzukiDF6D4FixedGridShard011OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard011OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
