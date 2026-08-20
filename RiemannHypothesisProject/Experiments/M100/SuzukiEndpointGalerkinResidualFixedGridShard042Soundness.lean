import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard042Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard042Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard042EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard042EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 42 k) := by
  have h := suzukiDF6D4FixedGridShard042Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard042EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 42 k)) at h
  exact h

def suzukiDF6D4FixedGridShard042EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard042EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard042EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard042EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard042EvenComparisonData)

theorem suzukiDF6D4FixedGridShard042EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard042EvenSolveData =
      suzukiDF6D4FixedGridShard042EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard042Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard042EvenSolveData =
    suzukiDF6D4FixedGridShard042EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard042EvenCross_eq_live :
    suzukiDF6D4FixedGridShard042EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 42) := by
  have h := suzukiDF6D4FixedGridShard042Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard042EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 42)) at h
  exact h

theorem suzukiDF6D4FixedGridShard042EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard042EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 42 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 42 k) := by
    rw [suzukiDF6D4FixedGridShard042EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 42 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042EvenDotSoundness i
          suzukiDF6D4FixedGridShard042EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 42 k) := by
    simpa [suzukiDF6D4FixedGridShard042EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard042EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 42 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 42) := by
    rw [suzukiDF6D4FixedGridShard042EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 42)
  rw [suzukiDF6D4FixedGridShard042EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard042EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard042EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard042EvenDotSoundness i
            suzukiDF6D4FixedGridShard042EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard042EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard042OddComparison_eq_live :
    suzukiDF6D4FixedGridShard042OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 42 k) := by
  have h := suzukiDF6D4FixedGridShard042Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard042OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 42 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard042OddCross_eq_live :
    suzukiDF6D4FixedGridShard042OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 42) := by
  have h := suzukiDF6D4FixedGridShard042Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard042OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 42)) at h
  exact h

def suzukiDF6D4FixedGridShard042OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard042OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard042OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard042OddDotSoundness i.val
      suzukiDF6D4FixedGridShard042OddComparisonData)

theorem suzukiDF6D4FixedGridShard042OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard042OddSolveData =
      suzukiDF6D4FixedGridShard042OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard042Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard042OddSolveData =
    suzukiDF6D4FixedGridShard042OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard042OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard042OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 42 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 42 k) := by
    rw [suzukiDF6D4FixedGridShard042OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 42 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042OddDotSoundness i
          suzukiDF6D4FixedGridShard042OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 42 k) := by
    simpa [suzukiDF6D4FixedGridShard042OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard042OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 42 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 42) := by
    rw [suzukiDF6D4FixedGridShard042OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 42)
  rw [suzukiDF6D4FixedGridShard042OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard042OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard042OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard042OddDotSoundness i
            suzukiDF6D4FixedGridShard042OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard042OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard042EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard042EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 343) := by
  have h := suzukiDF6D4FixedGridShard042Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard042EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 343)) at h
  exact h

theorem suzukiDF6D4FixedGridShard042EvenFull_eq_live :
    suzukiDF6D4FixedGridShard042EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 343) := by
  have h := suzukiDF6D4FixedGridShard042Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard042EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 343)) at h
  exact h

def suzukiDF6D4FixedGridShard042EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard042EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard042EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard042EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard042EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard042EvenResidualData =
      suzukiDF6D4FixedGridShard042EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard042Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard042EvenResidualData =
    suzukiDF6D4FixedGridShard042EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard042EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard042EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 343 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 343) := by
    rw [suzukiDF6D4FixedGridShard042EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 343
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042EvenDotSoundness i
          suzukiDF6D4FixedGridShard042EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 343) := by
    simpa [suzukiDF6D4FixedGridShard042EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard042EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 343) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 343) := by
    rw [suzukiDF6D4FixedGridShard042EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 343
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard042EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard042EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard042EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard042EvenDotSoundness i
            suzukiDF6D4FixedGridShard042EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard042EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard042OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard042OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 343) := by
  have h := suzukiDF6D4FixedGridShard042Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard042OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 343)) at h
  exact h

theorem suzukiDF6D4FixedGridShard042OddFull_eq_live :
    suzukiDF6D4FixedGridShard042OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 343) := by
  have h := suzukiDF6D4FixedGridShard042Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard042OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 343)) at h
  exact h

def suzukiDF6D4FixedGridShard042OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard042OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard042OddDotSoundness i.val
        suzukiDF6D4FixedGridShard042OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard042OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard042OddResidualData =
      suzukiDF6D4FixedGridShard042OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard042Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard042OddResidualData =
    suzukiDF6D4FixedGridShard042OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard042OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard042OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 343 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 343) := by
    rw [suzukiDF6D4FixedGridShard042OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 343
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042OddDotSoundness i
          suzukiDF6D4FixedGridShard042OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 343) := by
    simpa [suzukiDF6D4FixedGridShard042OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard042OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 343) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard042OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 343) := by
    rw [suzukiDF6D4FixedGridShard042OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 343
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard042OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard042OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard042OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard042OddDotSoundness i
            suzukiDF6D4FixedGridShard042OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard042OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
