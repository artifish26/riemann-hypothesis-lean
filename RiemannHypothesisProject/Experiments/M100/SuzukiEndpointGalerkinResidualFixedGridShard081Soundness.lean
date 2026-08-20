import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard081Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard081Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard081EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard081EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 81 k) := by
  have h := suzukiDF6D4FixedGridShard081Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard081EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 81 k)) at h
  exact h

def suzukiDF6D4FixedGridShard081EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard081EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard081EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard081EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard081EvenComparisonData)

theorem suzukiDF6D4FixedGridShard081EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard081EvenSolveData =
      suzukiDF6D4FixedGridShard081EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard081Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard081EvenSolveData =
    suzukiDF6D4FixedGridShard081EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard081EvenCross_eq_live :
    suzukiDF6D4FixedGridShard081EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 81) := by
  have h := suzukiDF6D4FixedGridShard081Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard081EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 81)) at h
  exact h

theorem suzukiDF6D4FixedGridShard081EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard081EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 81 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 81 k) := by
    rw [suzukiDF6D4FixedGridShard081EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 81 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081EvenDotSoundness i
          suzukiDF6D4FixedGridShard081EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 81 k) := by
    simpa [suzukiDF6D4FixedGridShard081EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard081EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 81 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 81) := by
    rw [suzukiDF6D4FixedGridShard081EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 81)
  rw [suzukiDF6D4FixedGridShard081EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard081EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard081EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard081EvenDotSoundness i
            suzukiDF6D4FixedGridShard081EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard081EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard081OddComparison_eq_live :
    suzukiDF6D4FixedGridShard081OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 81 k) := by
  have h := suzukiDF6D4FixedGridShard081Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard081OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 81 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard081OddCross_eq_live :
    suzukiDF6D4FixedGridShard081OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 81) := by
  have h := suzukiDF6D4FixedGridShard081Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard081OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 81)) at h
  exact h

def suzukiDF6D4FixedGridShard081OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard081OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard081OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard081OddDotSoundness i.val
      suzukiDF6D4FixedGridShard081OddComparisonData)

theorem suzukiDF6D4FixedGridShard081OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard081OddSolveData =
      suzukiDF6D4FixedGridShard081OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard081Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard081OddSolveData =
    suzukiDF6D4FixedGridShard081OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard081OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard081OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 81 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 81 k) := by
    rw [suzukiDF6D4FixedGridShard081OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 81 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081OddDotSoundness i
          suzukiDF6D4FixedGridShard081OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 81 k) := by
    simpa [suzukiDF6D4FixedGridShard081OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard081OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 81 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 81) := by
    rw [suzukiDF6D4FixedGridShard081OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 81)
  rw [suzukiDF6D4FixedGridShard081OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard081OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard081OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard081OddDotSoundness i
            suzukiDF6D4FixedGridShard081OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard081OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard081EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard081EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 382) := by
  have h := suzukiDF6D4FixedGridShard081Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard081EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 382)) at h
  exact h

theorem suzukiDF6D4FixedGridShard081EvenFull_eq_live :
    suzukiDF6D4FixedGridShard081EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 382) := by
  have h := suzukiDF6D4FixedGridShard081Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard081EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 382)) at h
  exact h

def suzukiDF6D4FixedGridShard081EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard081EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard081EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard081EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard081EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard081EvenResidualData =
      suzukiDF6D4FixedGridShard081EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard081Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard081EvenResidualData =
    suzukiDF6D4FixedGridShard081EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard081EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard081EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 382 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 382) := by
    rw [suzukiDF6D4FixedGridShard081EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 382
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081EvenDotSoundness i
          suzukiDF6D4FixedGridShard081EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 382) := by
    simpa [suzukiDF6D4FixedGridShard081EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard081EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 382) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 382) := by
    rw [suzukiDF6D4FixedGridShard081EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 382
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard081EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard081EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard081EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard081EvenDotSoundness i
            suzukiDF6D4FixedGridShard081EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard081EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard081OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard081OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 382) := by
  have h := suzukiDF6D4FixedGridShard081Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard081OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 382)) at h
  exact h

theorem suzukiDF6D4FixedGridShard081OddFull_eq_live :
    suzukiDF6D4FixedGridShard081OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 382) := by
  have h := suzukiDF6D4FixedGridShard081Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard081OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 382)) at h
  exact h

def suzukiDF6D4FixedGridShard081OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard081OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard081OddDotSoundness i.val
        suzukiDF6D4FixedGridShard081OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard081OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard081OddResidualData =
      suzukiDF6D4FixedGridShard081OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard081Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard081OddResidualData =
    suzukiDF6D4FixedGridShard081OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard081OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard081OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 382 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 382) := by
    rw [suzukiDF6D4FixedGridShard081OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 382
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081OddDotSoundness i
          suzukiDF6D4FixedGridShard081OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 382) := by
    simpa [suzukiDF6D4FixedGridShard081OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard081OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 382) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard081OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 382) := by
    rw [suzukiDF6D4FixedGridShard081OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 382
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard081OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard081OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard081OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard081OddDotSoundness i
            suzukiDF6D4FixedGridShard081OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard081OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
