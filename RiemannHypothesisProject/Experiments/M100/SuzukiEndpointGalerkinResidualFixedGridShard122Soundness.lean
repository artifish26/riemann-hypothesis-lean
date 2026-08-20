import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard122Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard122Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard122EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard122EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 122 k) := by
  have h := suzukiDF6D4FixedGridShard122Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard122EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 122 k)) at h
  exact h

def suzukiDF6D4FixedGridShard122EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard122EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard122EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard122EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard122EvenComparisonData)

theorem suzukiDF6D4FixedGridShard122EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard122EvenSolveData =
      suzukiDF6D4FixedGridShard122EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard122Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard122EvenSolveData =
    suzukiDF6D4FixedGridShard122EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard122EvenCross_eq_live :
    suzukiDF6D4FixedGridShard122EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 122) := by
  have h := suzukiDF6D4FixedGridShard122Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard122EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 122)) at h
  exact h

theorem suzukiDF6D4FixedGridShard122EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard122EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 122 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 122 k) := by
    rw [suzukiDF6D4FixedGridShard122EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 122 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122EvenDotSoundness i
          suzukiDF6D4FixedGridShard122EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 122 k) := by
    simpa [suzukiDF6D4FixedGridShard122EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard122EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 122 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 122) := by
    rw [suzukiDF6D4FixedGridShard122EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 122)
  rw [suzukiDF6D4FixedGridShard122EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard122EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard122EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard122EvenDotSoundness i
            suzukiDF6D4FixedGridShard122EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard122EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard122OddComparison_eq_live :
    suzukiDF6D4FixedGridShard122OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 122 k) := by
  have h := suzukiDF6D4FixedGridShard122Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard122OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 122 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard122OddCross_eq_live :
    suzukiDF6D4FixedGridShard122OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 122) := by
  have h := suzukiDF6D4FixedGridShard122Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard122OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 122)) at h
  exact h

def suzukiDF6D4FixedGridShard122OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard122OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard122OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard122OddDotSoundness i.val
      suzukiDF6D4FixedGridShard122OddComparisonData)

theorem suzukiDF6D4FixedGridShard122OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard122OddSolveData =
      suzukiDF6D4FixedGridShard122OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard122Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard122OddSolveData =
    suzukiDF6D4FixedGridShard122OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard122OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard122OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 122 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 122 k) := by
    rw [suzukiDF6D4FixedGridShard122OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 122 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122OddDotSoundness i
          suzukiDF6D4FixedGridShard122OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 122 k) := by
    simpa [suzukiDF6D4FixedGridShard122OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard122OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 122 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 122) := by
    rw [suzukiDF6D4FixedGridShard122OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 122)
  rw [suzukiDF6D4FixedGridShard122OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard122OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard122OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard122OddDotSoundness i
            suzukiDF6D4FixedGridShard122OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard122OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard122EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard122EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 423) := by
  have h := suzukiDF6D4FixedGridShard122Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard122EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 423)) at h
  exact h

theorem suzukiDF6D4FixedGridShard122EvenFull_eq_live :
    suzukiDF6D4FixedGridShard122EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 423) := by
  have h := suzukiDF6D4FixedGridShard122Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard122EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 423)) at h
  exact h

def suzukiDF6D4FixedGridShard122EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard122EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard122EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard122EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard122EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard122EvenResidualData =
      suzukiDF6D4FixedGridShard122EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard122Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard122EvenResidualData =
    suzukiDF6D4FixedGridShard122EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard122EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard122EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 423 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 423) := by
    rw [suzukiDF6D4FixedGridShard122EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 423
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122EvenDotSoundness i
          suzukiDF6D4FixedGridShard122EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 423) := by
    simpa [suzukiDF6D4FixedGridShard122EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard122EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 423) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 423) := by
    rw [suzukiDF6D4FixedGridShard122EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 423
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard122EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard122EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard122EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard122EvenDotSoundness i
            suzukiDF6D4FixedGridShard122EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard122EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard122OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard122OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 423) := by
  have h := suzukiDF6D4FixedGridShard122Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard122OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 423)) at h
  exact h

theorem suzukiDF6D4FixedGridShard122OddFull_eq_live :
    suzukiDF6D4FixedGridShard122OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 423) := by
  have h := suzukiDF6D4FixedGridShard122Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard122OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 423)) at h
  exact h

def suzukiDF6D4FixedGridShard122OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard122OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard122OddDotSoundness i.val
        suzukiDF6D4FixedGridShard122OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard122OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard122OddResidualData =
      suzukiDF6D4FixedGridShard122OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard122Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard122OddResidualData =
    suzukiDF6D4FixedGridShard122OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard122OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard122OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 423 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 423) := by
    rw [suzukiDF6D4FixedGridShard122OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 423
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122OddDotSoundness i
          suzukiDF6D4FixedGridShard122OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 423) := by
    simpa [suzukiDF6D4FixedGridShard122OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard122OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 423) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard122OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 423) := by
    rw [suzukiDF6D4FixedGridShard122OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 423
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard122OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard122OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard122OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard122OddDotSoundness i
            suzukiDF6D4FixedGridShard122OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard122OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
