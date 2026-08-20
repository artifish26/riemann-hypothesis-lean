import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard203Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard203Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard203EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard203EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 203 k) := by
  have h := suzukiDF6D4FixedGridShard203Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard203EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 203 k)) at h
  exact h

def suzukiDF6D4FixedGridShard203EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard203EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard203EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard203EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard203EvenComparisonData)

theorem suzukiDF6D4FixedGridShard203EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard203EvenSolveData =
      suzukiDF6D4FixedGridShard203EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard203Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard203EvenSolveData =
    suzukiDF6D4FixedGridShard203EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard203EvenCross_eq_live :
    suzukiDF6D4FixedGridShard203EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 203) := by
  have h := suzukiDF6D4FixedGridShard203Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard203EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 203)) at h
  exact h

theorem suzukiDF6D4FixedGridShard203EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard203EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 203 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 203 k) := by
    rw [suzukiDF6D4FixedGridShard203EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 203 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203EvenDotSoundness i
          suzukiDF6D4FixedGridShard203EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 203 k) := by
    simpa [suzukiDF6D4FixedGridShard203EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard203EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 203 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 203) := by
    rw [suzukiDF6D4FixedGridShard203EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 203)
  rw [suzukiDF6D4FixedGridShard203EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard203EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard203EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard203EvenDotSoundness i
            suzukiDF6D4FixedGridShard203EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard203EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard203OddComparison_eq_live :
    suzukiDF6D4FixedGridShard203OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 203 k) := by
  have h := suzukiDF6D4FixedGridShard203Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard203OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 203 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard203OddCross_eq_live :
    suzukiDF6D4FixedGridShard203OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 203) := by
  have h := suzukiDF6D4FixedGridShard203Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard203OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 203)) at h
  exact h

def suzukiDF6D4FixedGridShard203OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard203OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard203OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard203OddDotSoundness i.val
      suzukiDF6D4FixedGridShard203OddComparisonData)

theorem suzukiDF6D4FixedGridShard203OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard203OddSolveData =
      suzukiDF6D4FixedGridShard203OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard203Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard203OddSolveData =
    suzukiDF6D4FixedGridShard203OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard203OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard203OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 203 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 203 k) := by
    rw [suzukiDF6D4FixedGridShard203OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 203 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203OddDotSoundness i
          suzukiDF6D4FixedGridShard203OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 203 k) := by
    simpa [suzukiDF6D4FixedGridShard203OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard203OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 203 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 203) := by
    rw [suzukiDF6D4FixedGridShard203OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 203)
  rw [suzukiDF6D4FixedGridShard203OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard203OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard203OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard203OddDotSoundness i
            suzukiDF6D4FixedGridShard203OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard203OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard203EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard203EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 504) := by
  have h := suzukiDF6D4FixedGridShard203Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard203EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 504)) at h
  exact h

theorem suzukiDF6D4FixedGridShard203EvenFull_eq_live :
    suzukiDF6D4FixedGridShard203EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 504) := by
  have h := suzukiDF6D4FixedGridShard203Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard203EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 504)) at h
  exact h

def suzukiDF6D4FixedGridShard203EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard203EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard203EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard203EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard203EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard203EvenResidualData =
      suzukiDF6D4FixedGridShard203EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard203Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard203EvenResidualData =
    suzukiDF6D4FixedGridShard203EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard203EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard203EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 504 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 504) := by
    rw [suzukiDF6D4FixedGridShard203EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 504
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203EvenDotSoundness i
          suzukiDF6D4FixedGridShard203EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 504) := by
    simpa [suzukiDF6D4FixedGridShard203EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard203EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 504) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 504) := by
    rw [suzukiDF6D4FixedGridShard203EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 504
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard203EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard203EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard203EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard203EvenDotSoundness i
            suzukiDF6D4FixedGridShard203EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard203EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard203OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard203OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 504) := by
  have h := suzukiDF6D4FixedGridShard203Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard203OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 504)) at h
  exact h

theorem suzukiDF6D4FixedGridShard203OddFull_eq_live :
    suzukiDF6D4FixedGridShard203OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 504) := by
  have h := suzukiDF6D4FixedGridShard203Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard203OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 504)) at h
  exact h

def suzukiDF6D4FixedGridShard203OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard203OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard203OddDotSoundness i.val
        suzukiDF6D4FixedGridShard203OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard203OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard203OddResidualData =
      suzukiDF6D4FixedGridShard203OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard203Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard203OddResidualData =
    suzukiDF6D4FixedGridShard203OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard203OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard203OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 504 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 504) := by
    rw [suzukiDF6D4FixedGridShard203OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 504
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203OddDotSoundness i
          suzukiDF6D4FixedGridShard203OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 504) := by
    simpa [suzukiDF6D4FixedGridShard203OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard203OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 504) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard203OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 504) := by
    rw [suzukiDF6D4FixedGridShard203OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 504
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard203OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard203OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard203OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard203OddDotSoundness i
            suzukiDF6D4FixedGridShard203OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard203OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
