import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard066Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard066Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard066EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard066EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 66 k) := by
  have h := suzukiDF6D4FixedGridShard066Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard066EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 66 k)) at h
  exact h

def suzukiDF6D4FixedGridShard066EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard066EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard066EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard066EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard066EvenComparisonData)

theorem suzukiDF6D4FixedGridShard066EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard066EvenSolveData =
      suzukiDF6D4FixedGridShard066EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard066Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard066EvenSolveData =
    suzukiDF6D4FixedGridShard066EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard066EvenCross_eq_live :
    suzukiDF6D4FixedGridShard066EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 66) := by
  have h := suzukiDF6D4FixedGridShard066Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard066EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 66)) at h
  exact h

theorem suzukiDF6D4FixedGridShard066EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard066EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 66 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 66 k) := by
    rw [suzukiDF6D4FixedGridShard066EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 66 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066EvenDotSoundness i
          suzukiDF6D4FixedGridShard066EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 66 k) := by
    simpa [suzukiDF6D4FixedGridShard066EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard066EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 66 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 66) := by
    rw [suzukiDF6D4FixedGridShard066EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 66)
  rw [suzukiDF6D4FixedGridShard066EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard066EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard066EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard066EvenDotSoundness i
            suzukiDF6D4FixedGridShard066EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard066EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard066OddComparison_eq_live :
    suzukiDF6D4FixedGridShard066OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 66 k) := by
  have h := suzukiDF6D4FixedGridShard066Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard066OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 66 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard066OddCross_eq_live :
    suzukiDF6D4FixedGridShard066OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 66) := by
  have h := suzukiDF6D4FixedGridShard066Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard066OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 66)) at h
  exact h

def suzukiDF6D4FixedGridShard066OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard066OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard066OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard066OddDotSoundness i.val
      suzukiDF6D4FixedGridShard066OddComparisonData)

theorem suzukiDF6D4FixedGridShard066OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard066OddSolveData =
      suzukiDF6D4FixedGridShard066OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard066Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard066OddSolveData =
    suzukiDF6D4FixedGridShard066OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard066OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard066OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 66 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 66 k) := by
    rw [suzukiDF6D4FixedGridShard066OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 66 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066OddDotSoundness i
          suzukiDF6D4FixedGridShard066OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 66 k) := by
    simpa [suzukiDF6D4FixedGridShard066OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard066OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 66 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 66) := by
    rw [suzukiDF6D4FixedGridShard066OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 66)
  rw [suzukiDF6D4FixedGridShard066OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard066OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard066OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard066OddDotSoundness i
            suzukiDF6D4FixedGridShard066OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard066OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard066EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard066EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 367) := by
  have h := suzukiDF6D4FixedGridShard066Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard066EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 367)) at h
  exact h

theorem suzukiDF6D4FixedGridShard066EvenFull_eq_live :
    suzukiDF6D4FixedGridShard066EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 367) := by
  have h := suzukiDF6D4FixedGridShard066Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard066EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 367)) at h
  exact h

def suzukiDF6D4FixedGridShard066EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard066EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard066EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard066EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard066EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard066EvenResidualData =
      suzukiDF6D4FixedGridShard066EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard066Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard066EvenResidualData =
    suzukiDF6D4FixedGridShard066EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard066EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard066EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 367 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 367) := by
    rw [suzukiDF6D4FixedGridShard066EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 367
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066EvenDotSoundness i
          suzukiDF6D4FixedGridShard066EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 367) := by
    simpa [suzukiDF6D4FixedGridShard066EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard066EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 367) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 367) := by
    rw [suzukiDF6D4FixedGridShard066EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 367
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard066EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard066EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard066EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard066EvenDotSoundness i
            suzukiDF6D4FixedGridShard066EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard066EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard066OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard066OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 367) := by
  have h := suzukiDF6D4FixedGridShard066Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard066OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 367)) at h
  exact h

theorem suzukiDF6D4FixedGridShard066OddFull_eq_live :
    suzukiDF6D4FixedGridShard066OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 367) := by
  have h := suzukiDF6D4FixedGridShard066Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard066OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 367)) at h
  exact h

def suzukiDF6D4FixedGridShard066OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard066OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard066OddDotSoundness i.val
        suzukiDF6D4FixedGridShard066OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard066OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard066OddResidualData =
      suzukiDF6D4FixedGridShard066OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard066Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard066OddResidualData =
    suzukiDF6D4FixedGridShard066OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard066OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard066OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 367 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 367) := by
    rw [suzukiDF6D4FixedGridShard066OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 367
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066OddDotSoundness i
          suzukiDF6D4FixedGridShard066OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 367) := by
    simpa [suzukiDF6D4FixedGridShard066OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard066OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 367) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard066OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 367) := by
    rw [suzukiDF6D4FixedGridShard066OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 367
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard066OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard066OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard066OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard066OddDotSoundness i
            suzukiDF6D4FixedGridShard066OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard066OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
