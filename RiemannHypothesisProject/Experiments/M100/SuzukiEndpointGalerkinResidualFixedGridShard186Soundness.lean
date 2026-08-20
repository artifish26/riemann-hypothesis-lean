import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard186Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard186Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard186EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard186EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 186 k) := by
  have h := suzukiDF6D4FixedGridShard186Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard186EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 186 k)) at h
  exact h

def suzukiDF6D4FixedGridShard186EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard186EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard186EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard186EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard186EvenComparisonData)

theorem suzukiDF6D4FixedGridShard186EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard186EvenSolveData =
      suzukiDF6D4FixedGridShard186EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard186Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard186EvenSolveData =
    suzukiDF6D4FixedGridShard186EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard186EvenCross_eq_live :
    suzukiDF6D4FixedGridShard186EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 186) := by
  have h := suzukiDF6D4FixedGridShard186Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard186EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 186)) at h
  exact h

theorem suzukiDF6D4FixedGridShard186EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard186EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 186 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 186 k) := by
    rw [suzukiDF6D4FixedGridShard186EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 186 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186EvenDotSoundness i
          suzukiDF6D4FixedGridShard186EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 186 k) := by
    simpa [suzukiDF6D4FixedGridShard186EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard186EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 186 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 186) := by
    rw [suzukiDF6D4FixedGridShard186EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 186)
  rw [suzukiDF6D4FixedGridShard186EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard186EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard186EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard186EvenDotSoundness i
            suzukiDF6D4FixedGridShard186EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard186EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard186OddComparison_eq_live :
    suzukiDF6D4FixedGridShard186OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 186 k) := by
  have h := suzukiDF6D4FixedGridShard186Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard186OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 186 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard186OddCross_eq_live :
    suzukiDF6D4FixedGridShard186OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 186) := by
  have h := suzukiDF6D4FixedGridShard186Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard186OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 186)) at h
  exact h

def suzukiDF6D4FixedGridShard186OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard186OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard186OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard186OddDotSoundness i.val
      suzukiDF6D4FixedGridShard186OddComparisonData)

theorem suzukiDF6D4FixedGridShard186OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard186OddSolveData =
      suzukiDF6D4FixedGridShard186OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard186Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard186OddSolveData =
    suzukiDF6D4FixedGridShard186OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard186OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard186OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 186 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 186 k) := by
    rw [suzukiDF6D4FixedGridShard186OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 186 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186OddDotSoundness i
          suzukiDF6D4FixedGridShard186OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 186 k) := by
    simpa [suzukiDF6D4FixedGridShard186OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard186OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 186 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 186) := by
    rw [suzukiDF6D4FixedGridShard186OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 186)
  rw [suzukiDF6D4FixedGridShard186OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard186OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard186OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard186OddDotSoundness i
            suzukiDF6D4FixedGridShard186OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard186OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard186EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard186EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 487) := by
  have h := suzukiDF6D4FixedGridShard186Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard186EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 487)) at h
  exact h

theorem suzukiDF6D4FixedGridShard186EvenFull_eq_live :
    suzukiDF6D4FixedGridShard186EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 487) := by
  have h := suzukiDF6D4FixedGridShard186Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard186EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 487)) at h
  exact h

def suzukiDF6D4FixedGridShard186EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard186EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard186EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard186EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard186EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard186EvenResidualData =
      suzukiDF6D4FixedGridShard186EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard186Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard186EvenResidualData =
    suzukiDF6D4FixedGridShard186EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard186EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard186EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 487 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 487) := by
    rw [suzukiDF6D4FixedGridShard186EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 487
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186EvenDotSoundness i
          suzukiDF6D4FixedGridShard186EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 487) := by
    simpa [suzukiDF6D4FixedGridShard186EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard186EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 487) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 487) := by
    rw [suzukiDF6D4FixedGridShard186EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 487
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard186EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard186EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard186EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard186EvenDotSoundness i
            suzukiDF6D4FixedGridShard186EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard186EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard186OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard186OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 487) := by
  have h := suzukiDF6D4FixedGridShard186Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard186OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 487)) at h
  exact h

theorem suzukiDF6D4FixedGridShard186OddFull_eq_live :
    suzukiDF6D4FixedGridShard186OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 487) := by
  have h := suzukiDF6D4FixedGridShard186Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard186OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 487)) at h
  exact h

def suzukiDF6D4FixedGridShard186OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard186OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard186OddDotSoundness i.val
        suzukiDF6D4FixedGridShard186OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard186OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard186OddResidualData =
      suzukiDF6D4FixedGridShard186OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard186Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard186OddResidualData =
    suzukiDF6D4FixedGridShard186OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard186OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard186OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 487 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 487) := by
    rw [suzukiDF6D4FixedGridShard186OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 487
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186OddDotSoundness i
          suzukiDF6D4FixedGridShard186OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 487) := by
    simpa [suzukiDF6D4FixedGridShard186OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard186OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 487) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard186OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 487) := by
    rw [suzukiDF6D4FixedGridShard186OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 487
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard186OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard186OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard186OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard186OddDotSoundness i
            suzukiDF6D4FixedGridShard186OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard186OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
