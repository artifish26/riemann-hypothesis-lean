import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard224Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard224Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard224EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard224EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 224 k) := by
  have h := suzukiDF6D4FixedGridShard224Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard224EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 224 k)) at h
  exact h

def suzukiDF6D4FixedGridShard224EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard224EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard224EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard224EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard224EvenComparisonData)

theorem suzukiDF6D4FixedGridShard224EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard224EvenSolveData =
      suzukiDF6D4FixedGridShard224EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard224Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard224EvenSolveData =
    suzukiDF6D4FixedGridShard224EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard224EvenCross_eq_live :
    suzukiDF6D4FixedGridShard224EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 224) := by
  have h := suzukiDF6D4FixedGridShard224Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard224EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 224)) at h
  exact h

theorem suzukiDF6D4FixedGridShard224EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard224EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 224 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 224 k) := by
    rw [suzukiDF6D4FixedGridShard224EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 224 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224EvenDotSoundness i
          suzukiDF6D4FixedGridShard224EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 224 k) := by
    simpa [suzukiDF6D4FixedGridShard224EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard224EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 224 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 224) := by
    rw [suzukiDF6D4FixedGridShard224EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 224)
  rw [suzukiDF6D4FixedGridShard224EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard224EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard224EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard224EvenDotSoundness i
            suzukiDF6D4FixedGridShard224EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard224EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard224OddComparison_eq_live :
    suzukiDF6D4FixedGridShard224OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 224 k) := by
  have h := suzukiDF6D4FixedGridShard224Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard224OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 224 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard224OddCross_eq_live :
    suzukiDF6D4FixedGridShard224OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 224) := by
  have h := suzukiDF6D4FixedGridShard224Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard224OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 224)) at h
  exact h

def suzukiDF6D4FixedGridShard224OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard224OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard224OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard224OddDotSoundness i.val
      suzukiDF6D4FixedGridShard224OddComparisonData)

theorem suzukiDF6D4FixedGridShard224OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard224OddSolveData =
      suzukiDF6D4FixedGridShard224OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard224Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard224OddSolveData =
    suzukiDF6D4FixedGridShard224OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard224OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard224OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 224 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 224 k) := by
    rw [suzukiDF6D4FixedGridShard224OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 224 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224OddDotSoundness i
          suzukiDF6D4FixedGridShard224OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 224 k) := by
    simpa [suzukiDF6D4FixedGridShard224OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard224OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 224 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 224) := by
    rw [suzukiDF6D4FixedGridShard224OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 224)
  rw [suzukiDF6D4FixedGridShard224OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard224OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard224OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard224OddDotSoundness i
            suzukiDF6D4FixedGridShard224OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard224OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard224EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard224EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 525) := by
  have h := suzukiDF6D4FixedGridShard224Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard224EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 525)) at h
  exact h

theorem suzukiDF6D4FixedGridShard224EvenFull_eq_live :
    suzukiDF6D4FixedGridShard224EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 525) := by
  have h := suzukiDF6D4FixedGridShard224Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard224EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 525)) at h
  exact h

def suzukiDF6D4FixedGridShard224EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard224EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard224EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard224EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard224EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard224EvenResidualData =
      suzukiDF6D4FixedGridShard224EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard224Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard224EvenResidualData =
    suzukiDF6D4FixedGridShard224EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard224EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard224EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 525 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 525) := by
    rw [suzukiDF6D4FixedGridShard224EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 525
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224EvenDotSoundness i
          suzukiDF6D4FixedGridShard224EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 525) := by
    simpa [suzukiDF6D4FixedGridShard224EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard224EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 525) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 525) := by
    rw [suzukiDF6D4FixedGridShard224EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 525
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard224EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard224EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard224EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard224EvenDotSoundness i
            suzukiDF6D4FixedGridShard224EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard224EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard224OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard224OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 525) := by
  have h := suzukiDF6D4FixedGridShard224Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard224OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 525)) at h
  exact h

theorem suzukiDF6D4FixedGridShard224OddFull_eq_live :
    suzukiDF6D4FixedGridShard224OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 525) := by
  have h := suzukiDF6D4FixedGridShard224Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard224OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 525)) at h
  exact h

def suzukiDF6D4FixedGridShard224OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard224OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard224OddDotSoundness i.val
        suzukiDF6D4FixedGridShard224OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard224OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard224OddResidualData =
      suzukiDF6D4FixedGridShard224OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard224Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard224OddResidualData =
    suzukiDF6D4FixedGridShard224OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard224OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard224OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 525 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 525) := by
    rw [suzukiDF6D4FixedGridShard224OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 525
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224OddDotSoundness i
          suzukiDF6D4FixedGridShard224OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 525) := by
    simpa [suzukiDF6D4FixedGridShard224OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard224OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 525) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard224OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 525) := by
    rw [suzukiDF6D4FixedGridShard224OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 525
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard224OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard224OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard224OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard224OddDotSoundness i
            suzukiDF6D4FixedGridShard224OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard224OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
