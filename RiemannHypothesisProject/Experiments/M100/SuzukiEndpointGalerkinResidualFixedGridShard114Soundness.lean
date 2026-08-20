import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard114Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard114Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard114EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard114EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 114 k) := by
  have h := suzukiDF6D4FixedGridShard114Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard114EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 114 k)) at h
  exact h

def suzukiDF6D4FixedGridShard114EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard114EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard114EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard114EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard114EvenComparisonData)

theorem suzukiDF6D4FixedGridShard114EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard114EvenSolveData =
      suzukiDF6D4FixedGridShard114EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard114Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard114EvenSolveData =
    suzukiDF6D4FixedGridShard114EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard114EvenCross_eq_live :
    suzukiDF6D4FixedGridShard114EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 114) := by
  have h := suzukiDF6D4FixedGridShard114Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard114EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 114)) at h
  exact h

theorem suzukiDF6D4FixedGridShard114EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard114EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 114 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 114 k) := by
    rw [suzukiDF6D4FixedGridShard114EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 114 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114EvenDotSoundness i
          suzukiDF6D4FixedGridShard114EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 114 k) := by
    simpa [suzukiDF6D4FixedGridShard114EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard114EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 114 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 114) := by
    rw [suzukiDF6D4FixedGridShard114EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 114)
  rw [suzukiDF6D4FixedGridShard114EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard114EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard114EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard114EvenDotSoundness i
            suzukiDF6D4FixedGridShard114EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard114EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard114OddComparison_eq_live :
    suzukiDF6D4FixedGridShard114OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 114 k) := by
  have h := suzukiDF6D4FixedGridShard114Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard114OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 114 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard114OddCross_eq_live :
    suzukiDF6D4FixedGridShard114OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 114) := by
  have h := suzukiDF6D4FixedGridShard114Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard114OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 114)) at h
  exact h

def suzukiDF6D4FixedGridShard114OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard114OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard114OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard114OddDotSoundness i.val
      suzukiDF6D4FixedGridShard114OddComparisonData)

theorem suzukiDF6D4FixedGridShard114OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard114OddSolveData =
      suzukiDF6D4FixedGridShard114OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard114Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard114OddSolveData =
    suzukiDF6D4FixedGridShard114OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard114OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard114OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 114 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 114 k) := by
    rw [suzukiDF6D4FixedGridShard114OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 114 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114OddDotSoundness i
          suzukiDF6D4FixedGridShard114OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 114 k) := by
    simpa [suzukiDF6D4FixedGridShard114OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard114OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 114 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 114) := by
    rw [suzukiDF6D4FixedGridShard114OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 114)
  rw [suzukiDF6D4FixedGridShard114OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard114OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard114OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard114OddDotSoundness i
            suzukiDF6D4FixedGridShard114OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard114OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard114EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard114EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 415) := by
  have h := suzukiDF6D4FixedGridShard114Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard114EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 415)) at h
  exact h

theorem suzukiDF6D4FixedGridShard114EvenFull_eq_live :
    suzukiDF6D4FixedGridShard114EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 415) := by
  have h := suzukiDF6D4FixedGridShard114Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard114EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 415)) at h
  exact h

def suzukiDF6D4FixedGridShard114EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard114EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard114EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard114EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard114EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard114EvenResidualData =
      suzukiDF6D4FixedGridShard114EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard114Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard114EvenResidualData =
    suzukiDF6D4FixedGridShard114EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard114EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard114EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 415 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 415) := by
    rw [suzukiDF6D4FixedGridShard114EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 415
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114EvenDotSoundness i
          suzukiDF6D4FixedGridShard114EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 415) := by
    simpa [suzukiDF6D4FixedGridShard114EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard114EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 415) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 415) := by
    rw [suzukiDF6D4FixedGridShard114EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 415
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard114EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard114EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard114EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard114EvenDotSoundness i
            suzukiDF6D4FixedGridShard114EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard114EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard114OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard114OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 415) := by
  have h := suzukiDF6D4FixedGridShard114Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard114OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 415)) at h
  exact h

theorem suzukiDF6D4FixedGridShard114OddFull_eq_live :
    suzukiDF6D4FixedGridShard114OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 415) := by
  have h := suzukiDF6D4FixedGridShard114Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard114OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 415)) at h
  exact h

def suzukiDF6D4FixedGridShard114OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard114OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard114OddDotSoundness i.val
        suzukiDF6D4FixedGridShard114OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard114OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard114OddResidualData =
      suzukiDF6D4FixedGridShard114OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard114Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard114OddResidualData =
    suzukiDF6D4FixedGridShard114OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard114OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard114OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 415 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 415) := by
    rw [suzukiDF6D4FixedGridShard114OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 415
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114OddDotSoundness i
          suzukiDF6D4FixedGridShard114OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 415) := by
    simpa [suzukiDF6D4FixedGridShard114OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard114OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 415) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard114OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 415) := by
    rw [suzukiDF6D4FixedGridShard114OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 415
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard114OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard114OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard114OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard114OddDotSoundness i
            suzukiDF6D4FixedGridShard114OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard114OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
