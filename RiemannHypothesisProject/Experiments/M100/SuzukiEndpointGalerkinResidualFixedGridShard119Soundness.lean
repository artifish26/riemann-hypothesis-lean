import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard119Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard119Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard119EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard119EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 119 k) := by
  have h := suzukiDF6D4FixedGridShard119Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard119EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 119 k)) at h
  exact h

def suzukiDF6D4FixedGridShard119EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard119EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard119EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard119EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard119EvenComparisonData)

theorem suzukiDF6D4FixedGridShard119EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard119EvenSolveData =
      suzukiDF6D4FixedGridShard119EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard119Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard119EvenSolveData =
    suzukiDF6D4FixedGridShard119EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard119EvenCross_eq_live :
    suzukiDF6D4FixedGridShard119EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 119) := by
  have h := suzukiDF6D4FixedGridShard119Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard119EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 119)) at h
  exact h

theorem suzukiDF6D4FixedGridShard119EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard119EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 119 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 119 k) := by
    rw [suzukiDF6D4FixedGridShard119EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 119 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119EvenDotSoundness i
          suzukiDF6D4FixedGridShard119EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 119 k) := by
    simpa [suzukiDF6D4FixedGridShard119EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard119EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 119 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 119) := by
    rw [suzukiDF6D4FixedGridShard119EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 119)
  rw [suzukiDF6D4FixedGridShard119EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard119EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard119EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard119EvenDotSoundness i
            suzukiDF6D4FixedGridShard119EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard119EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard119OddComparison_eq_live :
    suzukiDF6D4FixedGridShard119OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 119 k) := by
  have h := suzukiDF6D4FixedGridShard119Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard119OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 119 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard119OddCross_eq_live :
    suzukiDF6D4FixedGridShard119OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 119) := by
  have h := suzukiDF6D4FixedGridShard119Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard119OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 119)) at h
  exact h

def suzukiDF6D4FixedGridShard119OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard119OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard119OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard119OddDotSoundness i.val
      suzukiDF6D4FixedGridShard119OddComparisonData)

theorem suzukiDF6D4FixedGridShard119OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard119OddSolveData =
      suzukiDF6D4FixedGridShard119OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard119Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard119OddSolveData =
    suzukiDF6D4FixedGridShard119OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard119OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard119OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 119 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 119 k) := by
    rw [suzukiDF6D4FixedGridShard119OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 119 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119OddDotSoundness i
          suzukiDF6D4FixedGridShard119OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 119 k) := by
    simpa [suzukiDF6D4FixedGridShard119OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard119OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 119 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 119) := by
    rw [suzukiDF6D4FixedGridShard119OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 119)
  rw [suzukiDF6D4FixedGridShard119OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard119OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard119OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard119OddDotSoundness i
            suzukiDF6D4FixedGridShard119OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard119OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard119EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard119EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 420) := by
  have h := suzukiDF6D4FixedGridShard119Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard119EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 420)) at h
  exact h

theorem suzukiDF6D4FixedGridShard119EvenFull_eq_live :
    suzukiDF6D4FixedGridShard119EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 420) := by
  have h := suzukiDF6D4FixedGridShard119Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard119EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 420)) at h
  exact h

def suzukiDF6D4FixedGridShard119EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard119EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard119EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard119EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard119EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard119EvenResidualData =
      suzukiDF6D4FixedGridShard119EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard119Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard119EvenResidualData =
    suzukiDF6D4FixedGridShard119EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard119EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard119EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 420 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 420) := by
    rw [suzukiDF6D4FixedGridShard119EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 420
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119EvenDotSoundness i
          suzukiDF6D4FixedGridShard119EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 420) := by
    simpa [suzukiDF6D4FixedGridShard119EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard119EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 420) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 420) := by
    rw [suzukiDF6D4FixedGridShard119EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 420
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard119EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard119EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard119EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard119EvenDotSoundness i
            suzukiDF6D4FixedGridShard119EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard119EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard119OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard119OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 420) := by
  have h := suzukiDF6D4FixedGridShard119Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard119OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 420)) at h
  exact h

theorem suzukiDF6D4FixedGridShard119OddFull_eq_live :
    suzukiDF6D4FixedGridShard119OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 420) := by
  have h := suzukiDF6D4FixedGridShard119Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard119OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 420)) at h
  exact h

def suzukiDF6D4FixedGridShard119OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard119OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard119OddDotSoundness i.val
        suzukiDF6D4FixedGridShard119OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard119OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard119OddResidualData =
      suzukiDF6D4FixedGridShard119OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard119Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard119OddResidualData =
    suzukiDF6D4FixedGridShard119OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard119OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard119OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 420 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 420) := by
    rw [suzukiDF6D4FixedGridShard119OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 420
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119OddDotSoundness i
          suzukiDF6D4FixedGridShard119OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 420) := by
    simpa [suzukiDF6D4FixedGridShard119OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard119OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 420) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard119OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 420) := by
    rw [suzukiDF6D4FixedGridShard119OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 420
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard119OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard119OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard119OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard119OddDotSoundness i
            suzukiDF6D4FixedGridShard119OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard119OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
