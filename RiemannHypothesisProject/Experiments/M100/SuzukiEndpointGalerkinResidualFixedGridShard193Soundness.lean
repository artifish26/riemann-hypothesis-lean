import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard193Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard193Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard193EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard193EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 193 k) := by
  have h := suzukiDF6D4FixedGridShard193Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard193EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 193 k)) at h
  exact h

def suzukiDF6D4FixedGridShard193EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard193EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard193EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard193EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard193EvenComparisonData)

theorem suzukiDF6D4FixedGridShard193EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard193EvenSolveData =
      suzukiDF6D4FixedGridShard193EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard193Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard193EvenSolveData =
    suzukiDF6D4FixedGridShard193EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard193EvenCross_eq_live :
    suzukiDF6D4FixedGridShard193EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 193) := by
  have h := suzukiDF6D4FixedGridShard193Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard193EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 193)) at h
  exact h

theorem suzukiDF6D4FixedGridShard193EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard193EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 193 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 193 k) := by
    rw [suzukiDF6D4FixedGridShard193EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 193 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193EvenDotSoundness i
          suzukiDF6D4FixedGridShard193EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 193 k) := by
    simpa [suzukiDF6D4FixedGridShard193EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard193EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 193 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 193) := by
    rw [suzukiDF6D4FixedGridShard193EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 193)
  rw [suzukiDF6D4FixedGridShard193EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard193EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard193EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard193EvenDotSoundness i
            suzukiDF6D4FixedGridShard193EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard193EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard193OddComparison_eq_live :
    suzukiDF6D4FixedGridShard193OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 193 k) := by
  have h := suzukiDF6D4FixedGridShard193Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard193OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 193 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard193OddCross_eq_live :
    suzukiDF6D4FixedGridShard193OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 193) := by
  have h := suzukiDF6D4FixedGridShard193Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard193OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 193)) at h
  exact h

def suzukiDF6D4FixedGridShard193OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard193OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard193OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard193OddDotSoundness i.val
      suzukiDF6D4FixedGridShard193OddComparisonData)

theorem suzukiDF6D4FixedGridShard193OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard193OddSolveData =
      suzukiDF6D4FixedGridShard193OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard193Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard193OddSolveData =
    suzukiDF6D4FixedGridShard193OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard193OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard193OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 193 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 193 k) := by
    rw [suzukiDF6D4FixedGridShard193OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 193 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193OddDotSoundness i
          suzukiDF6D4FixedGridShard193OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 193 k) := by
    simpa [suzukiDF6D4FixedGridShard193OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard193OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 193 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 193) := by
    rw [suzukiDF6D4FixedGridShard193OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 193)
  rw [suzukiDF6D4FixedGridShard193OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard193OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard193OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard193OddDotSoundness i
            suzukiDF6D4FixedGridShard193OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard193OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard193EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard193EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 494) := by
  have h := suzukiDF6D4FixedGridShard193Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard193EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 494)) at h
  exact h

theorem suzukiDF6D4FixedGridShard193EvenFull_eq_live :
    suzukiDF6D4FixedGridShard193EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 494) := by
  have h := suzukiDF6D4FixedGridShard193Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard193EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 494)) at h
  exact h

def suzukiDF6D4FixedGridShard193EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard193EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard193EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard193EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard193EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard193EvenResidualData =
      suzukiDF6D4FixedGridShard193EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard193Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard193EvenResidualData =
    suzukiDF6D4FixedGridShard193EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard193EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard193EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 494 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 494) := by
    rw [suzukiDF6D4FixedGridShard193EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 494
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193EvenDotSoundness i
          suzukiDF6D4FixedGridShard193EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 494) := by
    simpa [suzukiDF6D4FixedGridShard193EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard193EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 494) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 494) := by
    rw [suzukiDF6D4FixedGridShard193EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 494
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard193EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard193EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard193EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard193EvenDotSoundness i
            suzukiDF6D4FixedGridShard193EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard193EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard193OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard193OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 494) := by
  have h := suzukiDF6D4FixedGridShard193Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard193OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 494)) at h
  exact h

theorem suzukiDF6D4FixedGridShard193OddFull_eq_live :
    suzukiDF6D4FixedGridShard193OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 494) := by
  have h := suzukiDF6D4FixedGridShard193Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard193OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 494)) at h
  exact h

def suzukiDF6D4FixedGridShard193OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard193OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard193OddDotSoundness i.val
        suzukiDF6D4FixedGridShard193OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard193OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard193OddResidualData =
      suzukiDF6D4FixedGridShard193OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard193Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard193OddResidualData =
    suzukiDF6D4FixedGridShard193OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard193OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard193OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 494 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 494) := by
    rw [suzukiDF6D4FixedGridShard193OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 494
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193OddDotSoundness i
          suzukiDF6D4FixedGridShard193OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 494) := by
    simpa [suzukiDF6D4FixedGridShard193OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard193OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 494) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard193OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 494) := by
    rw [suzukiDF6D4FixedGridShard193OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 494
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard193OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard193OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard193OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard193OddDotSoundness i
            suzukiDF6D4FixedGridShard193OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard193OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
