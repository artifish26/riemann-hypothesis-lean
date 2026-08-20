import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard068Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard068Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard068EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard068EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 68 k) := by
  have h := suzukiDF6D4FixedGridShard068Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard068EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 68 k)) at h
  exact h

def suzukiDF6D4FixedGridShard068EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard068EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard068EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard068EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard068EvenComparisonData)

theorem suzukiDF6D4FixedGridShard068EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard068EvenSolveData =
      suzukiDF6D4FixedGridShard068EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard068Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard068EvenSolveData =
    suzukiDF6D4FixedGridShard068EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard068EvenCross_eq_live :
    suzukiDF6D4FixedGridShard068EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 68) := by
  have h := suzukiDF6D4FixedGridShard068Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard068EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 68)) at h
  exact h

theorem suzukiDF6D4FixedGridShard068EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard068EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 68 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 68 k) := by
    rw [suzukiDF6D4FixedGridShard068EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 68 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068EvenDotSoundness i
          suzukiDF6D4FixedGridShard068EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 68 k) := by
    simpa [suzukiDF6D4FixedGridShard068EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard068EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 68 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 68) := by
    rw [suzukiDF6D4FixedGridShard068EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 68)
  rw [suzukiDF6D4FixedGridShard068EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard068EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard068EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard068EvenDotSoundness i
            suzukiDF6D4FixedGridShard068EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard068EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard068OddComparison_eq_live :
    suzukiDF6D4FixedGridShard068OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 68 k) := by
  have h := suzukiDF6D4FixedGridShard068Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard068OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 68 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard068OddCross_eq_live :
    suzukiDF6D4FixedGridShard068OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 68) := by
  have h := suzukiDF6D4FixedGridShard068Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard068OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 68)) at h
  exact h

def suzukiDF6D4FixedGridShard068OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard068OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard068OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard068OddDotSoundness i.val
      suzukiDF6D4FixedGridShard068OddComparisonData)

theorem suzukiDF6D4FixedGridShard068OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard068OddSolveData =
      suzukiDF6D4FixedGridShard068OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard068Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard068OddSolveData =
    suzukiDF6D4FixedGridShard068OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard068OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard068OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 68 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 68 k) := by
    rw [suzukiDF6D4FixedGridShard068OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 68 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068OddDotSoundness i
          suzukiDF6D4FixedGridShard068OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 68 k) := by
    simpa [suzukiDF6D4FixedGridShard068OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard068OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 68 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 68) := by
    rw [suzukiDF6D4FixedGridShard068OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 68)
  rw [suzukiDF6D4FixedGridShard068OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard068OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard068OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard068OddDotSoundness i
            suzukiDF6D4FixedGridShard068OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard068OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard068EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard068EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 369) := by
  have h := suzukiDF6D4FixedGridShard068Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard068EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 369)) at h
  exact h

theorem suzukiDF6D4FixedGridShard068EvenFull_eq_live :
    suzukiDF6D4FixedGridShard068EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 369) := by
  have h := suzukiDF6D4FixedGridShard068Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard068EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 369)) at h
  exact h

def suzukiDF6D4FixedGridShard068EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard068EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard068EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard068EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard068EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard068EvenResidualData =
      suzukiDF6D4FixedGridShard068EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard068Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard068EvenResidualData =
    suzukiDF6D4FixedGridShard068EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard068EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard068EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 369 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 369) := by
    rw [suzukiDF6D4FixedGridShard068EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 369
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068EvenDotSoundness i
          suzukiDF6D4FixedGridShard068EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 369) := by
    simpa [suzukiDF6D4FixedGridShard068EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard068EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 369) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 369) := by
    rw [suzukiDF6D4FixedGridShard068EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 369
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard068EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard068EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard068EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard068EvenDotSoundness i
            suzukiDF6D4FixedGridShard068EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard068EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard068OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard068OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 369) := by
  have h := suzukiDF6D4FixedGridShard068Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard068OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 369)) at h
  exact h

theorem suzukiDF6D4FixedGridShard068OddFull_eq_live :
    suzukiDF6D4FixedGridShard068OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 369) := by
  have h := suzukiDF6D4FixedGridShard068Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard068OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 369)) at h
  exact h

def suzukiDF6D4FixedGridShard068OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard068OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard068OddDotSoundness i.val
        suzukiDF6D4FixedGridShard068OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard068OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard068OddResidualData =
      suzukiDF6D4FixedGridShard068OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard068Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard068OddResidualData =
    suzukiDF6D4FixedGridShard068OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard068OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard068OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 369 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 369) := by
    rw [suzukiDF6D4FixedGridShard068OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 369
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068OddDotSoundness i
          suzukiDF6D4FixedGridShard068OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 369) := by
    simpa [suzukiDF6D4FixedGridShard068OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard068OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 369) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard068OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 369) := by
    rw [suzukiDF6D4FixedGridShard068OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 369
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard068OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard068OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard068OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard068OddDotSoundness i
            suzukiDF6D4FixedGridShard068OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard068OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
