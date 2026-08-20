import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard069Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard069Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard069EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard069EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 69 k) := by
  have h := suzukiDF6D4FixedGridShard069Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard069EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 69 k)) at h
  exact h

def suzukiDF6D4FixedGridShard069EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard069EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard069EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard069EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard069EvenComparisonData)

theorem suzukiDF6D4FixedGridShard069EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard069EvenSolveData =
      suzukiDF6D4FixedGridShard069EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard069Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard069EvenSolveData =
    suzukiDF6D4FixedGridShard069EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard069EvenCross_eq_live :
    suzukiDF6D4FixedGridShard069EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 69) := by
  have h := suzukiDF6D4FixedGridShard069Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard069EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 69)) at h
  exact h

theorem suzukiDF6D4FixedGridShard069EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard069EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 69 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 69 k) := by
    rw [suzukiDF6D4FixedGridShard069EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 69 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069EvenDotSoundness i
          suzukiDF6D4FixedGridShard069EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 69 k) := by
    simpa [suzukiDF6D4FixedGridShard069EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard069EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 69 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 69) := by
    rw [suzukiDF6D4FixedGridShard069EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 69)
  rw [suzukiDF6D4FixedGridShard069EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard069EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard069EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard069EvenDotSoundness i
            suzukiDF6D4FixedGridShard069EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard069EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard069OddComparison_eq_live :
    suzukiDF6D4FixedGridShard069OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 69 k) := by
  have h := suzukiDF6D4FixedGridShard069Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard069OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 69 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard069OddCross_eq_live :
    suzukiDF6D4FixedGridShard069OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 69) := by
  have h := suzukiDF6D4FixedGridShard069Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard069OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 69)) at h
  exact h

def suzukiDF6D4FixedGridShard069OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard069OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard069OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard069OddDotSoundness i.val
      suzukiDF6D4FixedGridShard069OddComparisonData)

theorem suzukiDF6D4FixedGridShard069OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard069OddSolveData =
      suzukiDF6D4FixedGridShard069OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard069Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard069OddSolveData =
    suzukiDF6D4FixedGridShard069OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard069OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard069OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 69 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 69 k) := by
    rw [suzukiDF6D4FixedGridShard069OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 69 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069OddDotSoundness i
          suzukiDF6D4FixedGridShard069OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 69 k) := by
    simpa [suzukiDF6D4FixedGridShard069OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard069OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 69 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 69) := by
    rw [suzukiDF6D4FixedGridShard069OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 69)
  rw [suzukiDF6D4FixedGridShard069OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard069OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard069OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard069OddDotSoundness i
            suzukiDF6D4FixedGridShard069OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard069OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard069EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard069EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 370) := by
  have h := suzukiDF6D4FixedGridShard069Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard069EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 370)) at h
  exact h

theorem suzukiDF6D4FixedGridShard069EvenFull_eq_live :
    suzukiDF6D4FixedGridShard069EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 370) := by
  have h := suzukiDF6D4FixedGridShard069Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard069EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 370)) at h
  exact h

def suzukiDF6D4FixedGridShard069EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard069EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard069EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard069EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard069EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard069EvenResidualData =
      suzukiDF6D4FixedGridShard069EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard069Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard069EvenResidualData =
    suzukiDF6D4FixedGridShard069EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard069EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard069EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 370 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 370) := by
    rw [suzukiDF6D4FixedGridShard069EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 370
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069EvenDotSoundness i
          suzukiDF6D4FixedGridShard069EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 370) := by
    simpa [suzukiDF6D4FixedGridShard069EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard069EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 370) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 370) := by
    rw [suzukiDF6D4FixedGridShard069EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 370
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard069EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard069EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard069EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard069EvenDotSoundness i
            suzukiDF6D4FixedGridShard069EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard069EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard069OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard069OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 370) := by
  have h := suzukiDF6D4FixedGridShard069Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard069OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 370)) at h
  exact h

theorem suzukiDF6D4FixedGridShard069OddFull_eq_live :
    suzukiDF6D4FixedGridShard069OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 370) := by
  have h := suzukiDF6D4FixedGridShard069Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard069OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 370)) at h
  exact h

def suzukiDF6D4FixedGridShard069OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard069OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard069OddDotSoundness i.val
        suzukiDF6D4FixedGridShard069OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard069OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard069OddResidualData =
      suzukiDF6D4FixedGridShard069OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard069Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard069OddResidualData =
    suzukiDF6D4FixedGridShard069OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard069OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard069OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 370 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 370) := by
    rw [suzukiDF6D4FixedGridShard069OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 370
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069OddDotSoundness i
          suzukiDF6D4FixedGridShard069OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 370) := by
    simpa [suzukiDF6D4FixedGridShard069OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard069OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 370) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard069OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 370) := by
    rw [suzukiDF6D4FixedGridShard069OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 370
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard069OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard069OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard069OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard069OddDotSoundness i
            suzukiDF6D4FixedGridShard069OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard069OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
