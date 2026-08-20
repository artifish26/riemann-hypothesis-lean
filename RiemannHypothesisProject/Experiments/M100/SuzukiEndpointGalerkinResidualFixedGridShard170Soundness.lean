import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard170Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard170Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard170EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard170EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 170 k) := by
  have h := suzukiDF6D4FixedGridShard170Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard170EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 170 k)) at h
  exact h

def suzukiDF6D4FixedGridShard170EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard170EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard170EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard170EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard170EvenComparisonData)

theorem suzukiDF6D4FixedGridShard170EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard170EvenSolveData =
      suzukiDF6D4FixedGridShard170EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard170Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard170EvenSolveData =
    suzukiDF6D4FixedGridShard170EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard170EvenCross_eq_live :
    suzukiDF6D4FixedGridShard170EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 170) := by
  have h := suzukiDF6D4FixedGridShard170Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard170EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 170)) at h
  exact h

theorem suzukiDF6D4FixedGridShard170EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard170EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 170 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 170 k) := by
    rw [suzukiDF6D4FixedGridShard170EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 170 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170EvenDotSoundness i
          suzukiDF6D4FixedGridShard170EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 170 k) := by
    simpa [suzukiDF6D4FixedGridShard170EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard170EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 170 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 170) := by
    rw [suzukiDF6D4FixedGridShard170EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 170)
  rw [suzukiDF6D4FixedGridShard170EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard170EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard170EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard170EvenDotSoundness i
            suzukiDF6D4FixedGridShard170EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard170EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard170OddComparison_eq_live :
    suzukiDF6D4FixedGridShard170OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 170 k) := by
  have h := suzukiDF6D4FixedGridShard170Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard170OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 170 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard170OddCross_eq_live :
    suzukiDF6D4FixedGridShard170OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 170) := by
  have h := suzukiDF6D4FixedGridShard170Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard170OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 170)) at h
  exact h

def suzukiDF6D4FixedGridShard170OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard170OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard170OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard170OddDotSoundness i.val
      suzukiDF6D4FixedGridShard170OddComparisonData)

theorem suzukiDF6D4FixedGridShard170OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard170OddSolveData =
      suzukiDF6D4FixedGridShard170OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard170Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard170OddSolveData =
    suzukiDF6D4FixedGridShard170OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard170OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard170OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 170 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 170 k) := by
    rw [suzukiDF6D4FixedGridShard170OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 170 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170OddDotSoundness i
          suzukiDF6D4FixedGridShard170OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 170 k) := by
    simpa [suzukiDF6D4FixedGridShard170OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard170OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 170 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 170) := by
    rw [suzukiDF6D4FixedGridShard170OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 170)
  rw [suzukiDF6D4FixedGridShard170OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard170OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard170OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard170OddDotSoundness i
            suzukiDF6D4FixedGridShard170OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard170OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard170EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard170EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 471) := by
  have h := suzukiDF6D4FixedGridShard170Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard170EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 471)) at h
  exact h

theorem suzukiDF6D4FixedGridShard170EvenFull_eq_live :
    suzukiDF6D4FixedGridShard170EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 471) := by
  have h := suzukiDF6D4FixedGridShard170Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard170EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 471)) at h
  exact h

def suzukiDF6D4FixedGridShard170EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard170EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard170EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard170EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard170EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard170EvenResidualData =
      suzukiDF6D4FixedGridShard170EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard170Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard170EvenResidualData =
    suzukiDF6D4FixedGridShard170EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard170EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard170EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 471 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 471) := by
    rw [suzukiDF6D4FixedGridShard170EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 471
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170EvenDotSoundness i
          suzukiDF6D4FixedGridShard170EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 471) := by
    simpa [suzukiDF6D4FixedGridShard170EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard170EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 471) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 471) := by
    rw [suzukiDF6D4FixedGridShard170EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 471
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard170EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard170EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard170EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard170EvenDotSoundness i
            suzukiDF6D4FixedGridShard170EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard170EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard170OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard170OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 471) := by
  have h := suzukiDF6D4FixedGridShard170Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard170OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 471)) at h
  exact h

theorem suzukiDF6D4FixedGridShard170OddFull_eq_live :
    suzukiDF6D4FixedGridShard170OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 471) := by
  have h := suzukiDF6D4FixedGridShard170Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard170OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 471)) at h
  exact h

def suzukiDF6D4FixedGridShard170OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard170OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard170OddDotSoundness i.val
        suzukiDF6D4FixedGridShard170OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard170OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard170OddResidualData =
      suzukiDF6D4FixedGridShard170OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard170Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard170OddResidualData =
    suzukiDF6D4FixedGridShard170OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard170OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard170OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 471 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 471) := by
    rw [suzukiDF6D4FixedGridShard170OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 471
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170OddDotSoundness i
          suzukiDF6D4FixedGridShard170OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 471) := by
    simpa [suzukiDF6D4FixedGridShard170OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard170OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 471) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard170OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 471) := by
    rw [suzukiDF6D4FixedGridShard170OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 471
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard170OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard170OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard170OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard170OddDotSoundness i
            suzukiDF6D4FixedGridShard170OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard170OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
