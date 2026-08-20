import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard220Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard220Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard220EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard220EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 220 k) := by
  have h := suzukiDF6D4FixedGridShard220Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard220EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 220 k)) at h
  exact h

def suzukiDF6D4FixedGridShard220EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard220EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard220EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard220EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard220EvenComparisonData)

theorem suzukiDF6D4FixedGridShard220EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard220EvenSolveData =
      suzukiDF6D4FixedGridShard220EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard220Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard220EvenSolveData =
    suzukiDF6D4FixedGridShard220EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard220EvenCross_eq_live :
    suzukiDF6D4FixedGridShard220EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 220) := by
  have h := suzukiDF6D4FixedGridShard220Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard220EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 220)) at h
  exact h

theorem suzukiDF6D4FixedGridShard220EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard220EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 220 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 220 k) := by
    rw [suzukiDF6D4FixedGridShard220EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 220 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220EvenDotSoundness i
          suzukiDF6D4FixedGridShard220EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 220 k) := by
    simpa [suzukiDF6D4FixedGridShard220EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard220EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 220 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 220) := by
    rw [suzukiDF6D4FixedGridShard220EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 220)
  rw [suzukiDF6D4FixedGridShard220EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard220EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard220EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard220EvenDotSoundness i
            suzukiDF6D4FixedGridShard220EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard220EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard220OddComparison_eq_live :
    suzukiDF6D4FixedGridShard220OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 220 k) := by
  have h := suzukiDF6D4FixedGridShard220Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard220OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 220 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard220OddCross_eq_live :
    suzukiDF6D4FixedGridShard220OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 220) := by
  have h := suzukiDF6D4FixedGridShard220Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard220OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 220)) at h
  exact h

def suzukiDF6D4FixedGridShard220OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard220OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard220OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard220OddDotSoundness i.val
      suzukiDF6D4FixedGridShard220OddComparisonData)

theorem suzukiDF6D4FixedGridShard220OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard220OddSolveData =
      suzukiDF6D4FixedGridShard220OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard220Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard220OddSolveData =
    suzukiDF6D4FixedGridShard220OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard220OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard220OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 220 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 220 k) := by
    rw [suzukiDF6D4FixedGridShard220OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 220 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220OddDotSoundness i
          suzukiDF6D4FixedGridShard220OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 220 k) := by
    simpa [suzukiDF6D4FixedGridShard220OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard220OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 220 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 220) := by
    rw [suzukiDF6D4FixedGridShard220OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 220)
  rw [suzukiDF6D4FixedGridShard220OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard220OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard220OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard220OddDotSoundness i
            suzukiDF6D4FixedGridShard220OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard220OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard220EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard220EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 521) := by
  have h := suzukiDF6D4FixedGridShard220Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard220EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 521)) at h
  exact h

theorem suzukiDF6D4FixedGridShard220EvenFull_eq_live :
    suzukiDF6D4FixedGridShard220EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 521) := by
  have h := suzukiDF6D4FixedGridShard220Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard220EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 521)) at h
  exact h

def suzukiDF6D4FixedGridShard220EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard220EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard220EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard220EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard220EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard220EvenResidualData =
      suzukiDF6D4FixedGridShard220EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard220Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard220EvenResidualData =
    suzukiDF6D4FixedGridShard220EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard220EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard220EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 521 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 521) := by
    rw [suzukiDF6D4FixedGridShard220EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 521
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220EvenDotSoundness i
          suzukiDF6D4FixedGridShard220EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 521) := by
    simpa [suzukiDF6D4FixedGridShard220EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard220EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 521) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 521) := by
    rw [suzukiDF6D4FixedGridShard220EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 521
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard220EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard220EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard220EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard220EvenDotSoundness i
            suzukiDF6D4FixedGridShard220EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard220EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard220OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard220OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 521) := by
  have h := suzukiDF6D4FixedGridShard220Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard220OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 521)) at h
  exact h

theorem suzukiDF6D4FixedGridShard220OddFull_eq_live :
    suzukiDF6D4FixedGridShard220OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 521) := by
  have h := suzukiDF6D4FixedGridShard220Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard220OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 521)) at h
  exact h

def suzukiDF6D4FixedGridShard220OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard220OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard220OddDotSoundness i.val
        suzukiDF6D4FixedGridShard220OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard220OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard220OddResidualData =
      suzukiDF6D4FixedGridShard220OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard220Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard220OddResidualData =
    suzukiDF6D4FixedGridShard220OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard220OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard220OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 521 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 521) := by
    rw [suzukiDF6D4FixedGridShard220OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 521
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220OddDotSoundness i
          suzukiDF6D4FixedGridShard220OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 521) := by
    simpa [suzukiDF6D4FixedGridShard220OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard220OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 521) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard220OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 521) := by
    rw [suzukiDF6D4FixedGridShard220OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 521
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard220OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard220OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard220OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard220OddDotSoundness i
            suzukiDF6D4FixedGridShard220OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard220OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
