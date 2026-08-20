import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard071Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard071Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard071EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard071EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 71 k) := by
  have h := suzukiDF6D4FixedGridShard071Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard071EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 71 k)) at h
  exact h

def suzukiDF6D4FixedGridShard071EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard071EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard071EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard071EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard071EvenComparisonData)

theorem suzukiDF6D4FixedGridShard071EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard071EvenSolveData =
      suzukiDF6D4FixedGridShard071EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard071Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard071EvenSolveData =
    suzukiDF6D4FixedGridShard071EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard071EvenCross_eq_live :
    suzukiDF6D4FixedGridShard071EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 71) := by
  have h := suzukiDF6D4FixedGridShard071Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard071EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 71)) at h
  exact h

theorem suzukiDF6D4FixedGridShard071EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard071EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 71 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 71 k) := by
    rw [suzukiDF6D4FixedGridShard071EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 71 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071EvenDotSoundness i
          suzukiDF6D4FixedGridShard071EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 71 k) := by
    simpa [suzukiDF6D4FixedGridShard071EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard071EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 71 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 71) := by
    rw [suzukiDF6D4FixedGridShard071EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 71)
  rw [suzukiDF6D4FixedGridShard071EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard071EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard071EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard071EvenDotSoundness i
            suzukiDF6D4FixedGridShard071EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard071EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard071OddComparison_eq_live :
    suzukiDF6D4FixedGridShard071OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 71 k) := by
  have h := suzukiDF6D4FixedGridShard071Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard071OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 71 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard071OddCross_eq_live :
    suzukiDF6D4FixedGridShard071OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 71) := by
  have h := suzukiDF6D4FixedGridShard071Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard071OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 71)) at h
  exact h

def suzukiDF6D4FixedGridShard071OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard071OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard071OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard071OddDotSoundness i.val
      suzukiDF6D4FixedGridShard071OddComparisonData)

theorem suzukiDF6D4FixedGridShard071OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard071OddSolveData =
      suzukiDF6D4FixedGridShard071OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard071Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard071OddSolveData =
    suzukiDF6D4FixedGridShard071OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard071OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard071OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 71 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 71 k) := by
    rw [suzukiDF6D4FixedGridShard071OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 71 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071OddDotSoundness i
          suzukiDF6D4FixedGridShard071OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 71 k) := by
    simpa [suzukiDF6D4FixedGridShard071OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard071OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 71 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 71) := by
    rw [suzukiDF6D4FixedGridShard071OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 71)
  rw [suzukiDF6D4FixedGridShard071OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard071OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard071OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard071OddDotSoundness i
            suzukiDF6D4FixedGridShard071OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard071OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard071EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard071EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 372) := by
  have h := suzukiDF6D4FixedGridShard071Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard071EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 372)) at h
  exact h

theorem suzukiDF6D4FixedGridShard071EvenFull_eq_live :
    suzukiDF6D4FixedGridShard071EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 372) := by
  have h := suzukiDF6D4FixedGridShard071Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard071EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 372)) at h
  exact h

def suzukiDF6D4FixedGridShard071EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard071EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard071EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard071EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard071EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard071EvenResidualData =
      suzukiDF6D4FixedGridShard071EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard071Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard071EvenResidualData =
    suzukiDF6D4FixedGridShard071EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard071EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard071EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 372 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 372) := by
    rw [suzukiDF6D4FixedGridShard071EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 372
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071EvenDotSoundness i
          suzukiDF6D4FixedGridShard071EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 372) := by
    simpa [suzukiDF6D4FixedGridShard071EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard071EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 372) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 372) := by
    rw [suzukiDF6D4FixedGridShard071EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 372
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard071EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard071EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard071EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard071EvenDotSoundness i
            suzukiDF6D4FixedGridShard071EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard071EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard071OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard071OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 372) := by
  have h := suzukiDF6D4FixedGridShard071Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard071OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 372)) at h
  exact h

theorem suzukiDF6D4FixedGridShard071OddFull_eq_live :
    suzukiDF6D4FixedGridShard071OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 372) := by
  have h := suzukiDF6D4FixedGridShard071Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard071OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 372)) at h
  exact h

def suzukiDF6D4FixedGridShard071OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard071OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard071OddDotSoundness i.val
        suzukiDF6D4FixedGridShard071OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard071OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard071OddResidualData =
      suzukiDF6D4FixedGridShard071OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard071Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard071OddResidualData =
    suzukiDF6D4FixedGridShard071OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard071OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard071OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 372 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 372) := by
    rw [suzukiDF6D4FixedGridShard071OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 372
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071OddDotSoundness i
          suzukiDF6D4FixedGridShard071OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 372) := by
    simpa [suzukiDF6D4FixedGridShard071OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard071OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 372) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard071OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 372) := by
    rw [suzukiDF6D4FixedGridShard071OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 372
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard071OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard071OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard071OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard071OddDotSoundness i
            suzukiDF6D4FixedGridShard071OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard071OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
