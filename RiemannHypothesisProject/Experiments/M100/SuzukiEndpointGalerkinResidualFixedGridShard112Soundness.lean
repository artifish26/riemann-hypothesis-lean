import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard112Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard112Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard112EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard112EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 112 k) := by
  have h := suzukiDF6D4FixedGridShard112Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard112EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 112 k)) at h
  exact h

def suzukiDF6D4FixedGridShard112EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard112EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard112EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard112EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard112EvenComparisonData)

theorem suzukiDF6D4FixedGridShard112EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard112EvenSolveData =
      suzukiDF6D4FixedGridShard112EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard112Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard112EvenSolveData =
    suzukiDF6D4FixedGridShard112EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard112EvenCross_eq_live :
    suzukiDF6D4FixedGridShard112EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 112) := by
  have h := suzukiDF6D4FixedGridShard112Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard112EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 112)) at h
  exact h

theorem suzukiDF6D4FixedGridShard112EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard112EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 112 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 112 k) := by
    rw [suzukiDF6D4FixedGridShard112EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 112 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112EvenDotSoundness i
          suzukiDF6D4FixedGridShard112EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 112 k) := by
    simpa [suzukiDF6D4FixedGridShard112EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard112EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 112 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 112) := by
    rw [suzukiDF6D4FixedGridShard112EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 112)
  rw [suzukiDF6D4FixedGridShard112EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard112EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard112EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard112EvenDotSoundness i
            suzukiDF6D4FixedGridShard112EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard112EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard112OddComparison_eq_live :
    suzukiDF6D4FixedGridShard112OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 112 k) := by
  have h := suzukiDF6D4FixedGridShard112Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard112OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 112 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard112OddCross_eq_live :
    suzukiDF6D4FixedGridShard112OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 112) := by
  have h := suzukiDF6D4FixedGridShard112Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard112OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 112)) at h
  exact h

def suzukiDF6D4FixedGridShard112OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard112OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard112OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard112OddDotSoundness i.val
      suzukiDF6D4FixedGridShard112OddComparisonData)

theorem suzukiDF6D4FixedGridShard112OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard112OddSolveData =
      suzukiDF6D4FixedGridShard112OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard112Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard112OddSolveData =
    suzukiDF6D4FixedGridShard112OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard112OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard112OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 112 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 112 k) := by
    rw [suzukiDF6D4FixedGridShard112OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 112 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112OddDotSoundness i
          suzukiDF6D4FixedGridShard112OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 112 k) := by
    simpa [suzukiDF6D4FixedGridShard112OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard112OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 112 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 112) := by
    rw [suzukiDF6D4FixedGridShard112OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 112)
  rw [suzukiDF6D4FixedGridShard112OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard112OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard112OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard112OddDotSoundness i
            suzukiDF6D4FixedGridShard112OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard112OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard112EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard112EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 413) := by
  have h := suzukiDF6D4FixedGridShard112Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard112EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 413)) at h
  exact h

theorem suzukiDF6D4FixedGridShard112EvenFull_eq_live :
    suzukiDF6D4FixedGridShard112EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 413) := by
  have h := suzukiDF6D4FixedGridShard112Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard112EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 413)) at h
  exact h

def suzukiDF6D4FixedGridShard112EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard112EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard112EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard112EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard112EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard112EvenResidualData =
      suzukiDF6D4FixedGridShard112EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard112Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard112EvenResidualData =
    suzukiDF6D4FixedGridShard112EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard112EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard112EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 413 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 413) := by
    rw [suzukiDF6D4FixedGridShard112EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 413
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112EvenDotSoundness i
          suzukiDF6D4FixedGridShard112EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 413) := by
    simpa [suzukiDF6D4FixedGridShard112EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard112EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 413) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 413) := by
    rw [suzukiDF6D4FixedGridShard112EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 413
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard112EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard112EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard112EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard112EvenDotSoundness i
            suzukiDF6D4FixedGridShard112EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard112EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard112OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard112OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 413) := by
  have h := suzukiDF6D4FixedGridShard112Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard112OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 413)) at h
  exact h

theorem suzukiDF6D4FixedGridShard112OddFull_eq_live :
    suzukiDF6D4FixedGridShard112OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 413) := by
  have h := suzukiDF6D4FixedGridShard112Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard112OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 413)) at h
  exact h

def suzukiDF6D4FixedGridShard112OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard112OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard112OddDotSoundness i.val
        suzukiDF6D4FixedGridShard112OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard112OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard112OddResidualData =
      suzukiDF6D4FixedGridShard112OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard112Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard112OddResidualData =
    suzukiDF6D4FixedGridShard112OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard112OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard112OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 413 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 413) := by
    rw [suzukiDF6D4FixedGridShard112OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 413
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112OddDotSoundness i
          suzukiDF6D4FixedGridShard112OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 413) := by
    simpa [suzukiDF6D4FixedGridShard112OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard112OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 413) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard112OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 413) := by
    rw [suzukiDF6D4FixedGridShard112OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 413
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard112OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard112OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard112OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard112OddDotSoundness i
            suzukiDF6D4FixedGridShard112OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard112OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
