import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard048Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard048Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard048EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard048EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 48 k) := by
  have h := suzukiDF6D4FixedGridShard048Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard048EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 48 k)) at h
  exact h

def suzukiDF6D4FixedGridShard048EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard048EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard048EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard048EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard048EvenComparisonData)

theorem suzukiDF6D4FixedGridShard048EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard048EvenSolveData =
      suzukiDF6D4FixedGridShard048EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard048Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard048EvenSolveData =
    suzukiDF6D4FixedGridShard048EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard048EvenCross_eq_live :
    suzukiDF6D4FixedGridShard048EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 48) := by
  have h := suzukiDF6D4FixedGridShard048Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard048EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 48)) at h
  exact h

theorem suzukiDF6D4FixedGridShard048EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard048EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 48 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 48 k) := by
    rw [suzukiDF6D4FixedGridShard048EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 48 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048EvenDotSoundness i
          suzukiDF6D4FixedGridShard048EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 48 k) := by
    simpa [suzukiDF6D4FixedGridShard048EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard048EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 48 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 48) := by
    rw [suzukiDF6D4FixedGridShard048EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 48)
  rw [suzukiDF6D4FixedGridShard048EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard048EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard048EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard048EvenDotSoundness i
            suzukiDF6D4FixedGridShard048EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard048EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard048OddComparison_eq_live :
    suzukiDF6D4FixedGridShard048OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 48 k) := by
  have h := suzukiDF6D4FixedGridShard048Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard048OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 48 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard048OddCross_eq_live :
    suzukiDF6D4FixedGridShard048OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 48) := by
  have h := suzukiDF6D4FixedGridShard048Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard048OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 48)) at h
  exact h

def suzukiDF6D4FixedGridShard048OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard048OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard048OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard048OddDotSoundness i.val
      suzukiDF6D4FixedGridShard048OddComparisonData)

theorem suzukiDF6D4FixedGridShard048OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard048OddSolveData =
      suzukiDF6D4FixedGridShard048OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard048Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard048OddSolveData =
    suzukiDF6D4FixedGridShard048OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard048OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard048OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 48 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 48 k) := by
    rw [suzukiDF6D4FixedGridShard048OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 48 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048OddDotSoundness i
          suzukiDF6D4FixedGridShard048OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 48 k) := by
    simpa [suzukiDF6D4FixedGridShard048OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard048OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 48 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 48) := by
    rw [suzukiDF6D4FixedGridShard048OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 48)
  rw [suzukiDF6D4FixedGridShard048OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard048OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard048OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard048OddDotSoundness i
            suzukiDF6D4FixedGridShard048OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard048OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard048EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard048EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 349) := by
  have h := suzukiDF6D4FixedGridShard048Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard048EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 349)) at h
  exact h

theorem suzukiDF6D4FixedGridShard048EvenFull_eq_live :
    suzukiDF6D4FixedGridShard048EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 349) := by
  have h := suzukiDF6D4FixedGridShard048Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard048EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 349)) at h
  exact h

def suzukiDF6D4FixedGridShard048EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard048EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard048EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard048EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard048EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard048EvenResidualData =
      suzukiDF6D4FixedGridShard048EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard048Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard048EvenResidualData =
    suzukiDF6D4FixedGridShard048EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard048EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard048EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 349 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 349) := by
    rw [suzukiDF6D4FixedGridShard048EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 349
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048EvenDotSoundness i
          suzukiDF6D4FixedGridShard048EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 349) := by
    simpa [suzukiDF6D4FixedGridShard048EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard048EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 349) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 349) := by
    rw [suzukiDF6D4FixedGridShard048EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 349
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard048EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard048EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard048EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard048EvenDotSoundness i
            suzukiDF6D4FixedGridShard048EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard048EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard048OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard048OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 349) := by
  have h := suzukiDF6D4FixedGridShard048Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard048OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 349)) at h
  exact h

theorem suzukiDF6D4FixedGridShard048OddFull_eq_live :
    suzukiDF6D4FixedGridShard048OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 349) := by
  have h := suzukiDF6D4FixedGridShard048Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard048OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 349)) at h
  exact h

def suzukiDF6D4FixedGridShard048OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard048OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard048OddDotSoundness i.val
        suzukiDF6D4FixedGridShard048OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard048OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard048OddResidualData =
      suzukiDF6D4FixedGridShard048OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard048Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard048OddResidualData =
    suzukiDF6D4FixedGridShard048OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard048OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard048OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 349 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 349) := by
    rw [suzukiDF6D4FixedGridShard048OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 349
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048OddDotSoundness i
          suzukiDF6D4FixedGridShard048OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 349) := by
    simpa [suzukiDF6D4FixedGridShard048OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard048OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 349) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard048OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 349) := by
    rw [suzukiDF6D4FixedGridShard048OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 349
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard048OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard048OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard048OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard048OddDotSoundness i
            suzukiDF6D4FixedGridShard048OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard048OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
