import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard061Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard061Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard061EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard061EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 61 k) := by
  have h := suzukiDF6D4FixedGridShard061Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard061EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 61 k)) at h
  exact h

def suzukiDF6D4FixedGridShard061EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard061EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard061EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard061EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard061EvenComparisonData)

theorem suzukiDF6D4FixedGridShard061EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard061EvenSolveData =
      suzukiDF6D4FixedGridShard061EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard061Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard061EvenSolveData =
    suzukiDF6D4FixedGridShard061EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard061EvenCross_eq_live :
    suzukiDF6D4FixedGridShard061EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 61) := by
  have h := suzukiDF6D4FixedGridShard061Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard061EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 61)) at h
  exact h

theorem suzukiDF6D4FixedGridShard061EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard061EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 61 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 61 k) := by
    rw [suzukiDF6D4FixedGridShard061EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 61 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061EvenDotSoundness i
          suzukiDF6D4FixedGridShard061EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 61 k) := by
    simpa [suzukiDF6D4FixedGridShard061EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard061EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 61 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 61) := by
    rw [suzukiDF6D4FixedGridShard061EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 61)
  rw [suzukiDF6D4FixedGridShard061EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard061EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard061EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard061EvenDotSoundness i
            suzukiDF6D4FixedGridShard061EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard061EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard061OddComparison_eq_live :
    suzukiDF6D4FixedGridShard061OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 61 k) := by
  have h := suzukiDF6D4FixedGridShard061Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard061OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 61 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard061OddCross_eq_live :
    suzukiDF6D4FixedGridShard061OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 61) := by
  have h := suzukiDF6D4FixedGridShard061Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard061OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 61)) at h
  exact h

def suzukiDF6D4FixedGridShard061OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard061OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard061OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard061OddDotSoundness i.val
      suzukiDF6D4FixedGridShard061OddComparisonData)

theorem suzukiDF6D4FixedGridShard061OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard061OddSolveData =
      suzukiDF6D4FixedGridShard061OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard061Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard061OddSolveData =
    suzukiDF6D4FixedGridShard061OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard061OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard061OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 61 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 61 k) := by
    rw [suzukiDF6D4FixedGridShard061OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 61 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061OddDotSoundness i
          suzukiDF6D4FixedGridShard061OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 61 k) := by
    simpa [suzukiDF6D4FixedGridShard061OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard061OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 61 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 61) := by
    rw [suzukiDF6D4FixedGridShard061OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 61)
  rw [suzukiDF6D4FixedGridShard061OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard061OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard061OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard061OddDotSoundness i
            suzukiDF6D4FixedGridShard061OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard061OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard061EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard061EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 362) := by
  have h := suzukiDF6D4FixedGridShard061Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard061EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 362)) at h
  exact h

theorem suzukiDF6D4FixedGridShard061EvenFull_eq_live :
    suzukiDF6D4FixedGridShard061EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 362) := by
  have h := suzukiDF6D4FixedGridShard061Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard061EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 362)) at h
  exact h

def suzukiDF6D4FixedGridShard061EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard061EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard061EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard061EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard061EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard061EvenResidualData =
      suzukiDF6D4FixedGridShard061EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard061Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard061EvenResidualData =
    suzukiDF6D4FixedGridShard061EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard061EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard061EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 362 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 362) := by
    rw [suzukiDF6D4FixedGridShard061EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 362
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061EvenDotSoundness i
          suzukiDF6D4FixedGridShard061EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 362) := by
    simpa [suzukiDF6D4FixedGridShard061EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard061EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 362) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 362) := by
    rw [suzukiDF6D4FixedGridShard061EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 362
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard061EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard061EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard061EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard061EvenDotSoundness i
            suzukiDF6D4FixedGridShard061EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard061EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard061OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard061OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 362) := by
  have h := suzukiDF6D4FixedGridShard061Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard061OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 362)) at h
  exact h

theorem suzukiDF6D4FixedGridShard061OddFull_eq_live :
    suzukiDF6D4FixedGridShard061OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 362) := by
  have h := suzukiDF6D4FixedGridShard061Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard061OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 362)) at h
  exact h

def suzukiDF6D4FixedGridShard061OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard061OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard061OddDotSoundness i.val
        suzukiDF6D4FixedGridShard061OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard061OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard061OddResidualData =
      suzukiDF6D4FixedGridShard061OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard061Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard061OddResidualData =
    suzukiDF6D4FixedGridShard061OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard061OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard061OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 362 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 362) := by
    rw [suzukiDF6D4FixedGridShard061OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 362
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061OddDotSoundness i
          suzukiDF6D4FixedGridShard061OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 362) := by
    simpa [suzukiDF6D4FixedGridShard061OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard061OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 362) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard061OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 362) := by
    rw [suzukiDF6D4FixedGridShard061OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 362
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard061OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard061OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard061OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard061OddDotSoundness i
            suzukiDF6D4FixedGridShard061OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard061OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
