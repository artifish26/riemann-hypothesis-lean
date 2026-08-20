import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard109Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard109Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard109EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard109EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 109 k) := by
  have h := suzukiDF6D4FixedGridShard109Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard109EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 109 k)) at h
  exact h

def suzukiDF6D4FixedGridShard109EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard109EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard109EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard109EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard109EvenComparisonData)

theorem suzukiDF6D4FixedGridShard109EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard109EvenSolveData =
      suzukiDF6D4FixedGridShard109EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard109Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard109EvenSolveData =
    suzukiDF6D4FixedGridShard109EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard109EvenCross_eq_live :
    suzukiDF6D4FixedGridShard109EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 109) := by
  have h := suzukiDF6D4FixedGridShard109Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard109EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 109)) at h
  exact h

theorem suzukiDF6D4FixedGridShard109EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard109EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 109 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 109 k) := by
    rw [suzukiDF6D4FixedGridShard109EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 109 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109EvenDotSoundness i
          suzukiDF6D4FixedGridShard109EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 109 k) := by
    simpa [suzukiDF6D4FixedGridShard109EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard109EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 109 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 109) := by
    rw [suzukiDF6D4FixedGridShard109EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 109)
  rw [suzukiDF6D4FixedGridShard109EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard109EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard109EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard109EvenDotSoundness i
            suzukiDF6D4FixedGridShard109EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard109EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard109OddComparison_eq_live :
    suzukiDF6D4FixedGridShard109OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 109 k) := by
  have h := suzukiDF6D4FixedGridShard109Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard109OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 109 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard109OddCross_eq_live :
    suzukiDF6D4FixedGridShard109OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 109) := by
  have h := suzukiDF6D4FixedGridShard109Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard109OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 109)) at h
  exact h

def suzukiDF6D4FixedGridShard109OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard109OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard109OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard109OddDotSoundness i.val
      suzukiDF6D4FixedGridShard109OddComparisonData)

theorem suzukiDF6D4FixedGridShard109OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard109OddSolveData =
      suzukiDF6D4FixedGridShard109OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard109Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard109OddSolveData =
    suzukiDF6D4FixedGridShard109OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard109OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard109OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 109 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 109 k) := by
    rw [suzukiDF6D4FixedGridShard109OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 109 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109OddDotSoundness i
          suzukiDF6D4FixedGridShard109OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 109 k) := by
    simpa [suzukiDF6D4FixedGridShard109OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard109OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 109 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 109) := by
    rw [suzukiDF6D4FixedGridShard109OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 109)
  rw [suzukiDF6D4FixedGridShard109OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard109OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard109OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard109OddDotSoundness i
            suzukiDF6D4FixedGridShard109OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard109OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard109EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard109EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 410) := by
  have h := suzukiDF6D4FixedGridShard109Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard109EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 410)) at h
  exact h

theorem suzukiDF6D4FixedGridShard109EvenFull_eq_live :
    suzukiDF6D4FixedGridShard109EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 410) := by
  have h := suzukiDF6D4FixedGridShard109Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard109EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 410)) at h
  exact h

def suzukiDF6D4FixedGridShard109EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard109EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard109EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard109EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard109EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard109EvenResidualData =
      suzukiDF6D4FixedGridShard109EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard109Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard109EvenResidualData =
    suzukiDF6D4FixedGridShard109EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard109EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard109EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 410 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 410) := by
    rw [suzukiDF6D4FixedGridShard109EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 410
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109EvenDotSoundness i
          suzukiDF6D4FixedGridShard109EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 410) := by
    simpa [suzukiDF6D4FixedGridShard109EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard109EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 410) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 410) := by
    rw [suzukiDF6D4FixedGridShard109EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 410
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard109EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard109EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard109EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard109EvenDotSoundness i
            suzukiDF6D4FixedGridShard109EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard109EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard109OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard109OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 410) := by
  have h := suzukiDF6D4FixedGridShard109Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard109OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 410)) at h
  exact h

theorem suzukiDF6D4FixedGridShard109OddFull_eq_live :
    suzukiDF6D4FixedGridShard109OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 410) := by
  have h := suzukiDF6D4FixedGridShard109Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard109OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 410)) at h
  exact h

def suzukiDF6D4FixedGridShard109OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard109OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard109OddDotSoundness i.val
        suzukiDF6D4FixedGridShard109OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard109OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard109OddResidualData =
      suzukiDF6D4FixedGridShard109OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard109Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard109OddResidualData =
    suzukiDF6D4FixedGridShard109OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard109OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard109OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 410 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 410) := by
    rw [suzukiDF6D4FixedGridShard109OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 410
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109OddDotSoundness i
          suzukiDF6D4FixedGridShard109OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 410) := by
    simpa [suzukiDF6D4FixedGridShard109OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard109OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 410) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard109OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 410) := by
    rw [suzukiDF6D4FixedGridShard109OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 410
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard109OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard109OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard109OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard109OddDotSoundness i
            suzukiDF6D4FixedGridShard109OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard109OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
