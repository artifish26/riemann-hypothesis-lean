import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard140Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard140Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard140EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard140EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 140 k) := by
  have h := suzukiDF6D4FixedGridShard140Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard140EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 140 k)) at h
  exact h

def suzukiDF6D4FixedGridShard140EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard140EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard140EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard140EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard140EvenComparisonData)

theorem suzukiDF6D4FixedGridShard140EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard140EvenSolveData =
      suzukiDF6D4FixedGridShard140EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard140Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard140EvenSolveData =
    suzukiDF6D4FixedGridShard140EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard140EvenCross_eq_live :
    suzukiDF6D4FixedGridShard140EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 140) := by
  have h := suzukiDF6D4FixedGridShard140Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard140EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 140)) at h
  exact h

theorem suzukiDF6D4FixedGridShard140EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard140EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 140 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 140 k) := by
    rw [suzukiDF6D4FixedGridShard140EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 140 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140EvenDotSoundness i
          suzukiDF6D4FixedGridShard140EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 140 k) := by
    simpa [suzukiDF6D4FixedGridShard140EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard140EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 140 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 140) := by
    rw [suzukiDF6D4FixedGridShard140EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 140)
  rw [suzukiDF6D4FixedGridShard140EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard140EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard140EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard140EvenDotSoundness i
            suzukiDF6D4FixedGridShard140EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard140EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard140OddComparison_eq_live :
    suzukiDF6D4FixedGridShard140OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 140 k) := by
  have h := suzukiDF6D4FixedGridShard140Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard140OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 140 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard140OddCross_eq_live :
    suzukiDF6D4FixedGridShard140OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 140) := by
  have h := suzukiDF6D4FixedGridShard140Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard140OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 140)) at h
  exact h

def suzukiDF6D4FixedGridShard140OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard140OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard140OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard140OddDotSoundness i.val
      suzukiDF6D4FixedGridShard140OddComparisonData)

theorem suzukiDF6D4FixedGridShard140OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard140OddSolveData =
      suzukiDF6D4FixedGridShard140OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard140Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard140OddSolveData =
    suzukiDF6D4FixedGridShard140OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard140OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard140OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 140 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 140 k) := by
    rw [suzukiDF6D4FixedGridShard140OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 140 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140OddDotSoundness i
          suzukiDF6D4FixedGridShard140OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 140 k) := by
    simpa [suzukiDF6D4FixedGridShard140OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard140OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 140 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 140) := by
    rw [suzukiDF6D4FixedGridShard140OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 140)
  rw [suzukiDF6D4FixedGridShard140OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard140OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard140OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard140OddDotSoundness i
            suzukiDF6D4FixedGridShard140OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard140OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard140EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard140EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 441) := by
  have h := suzukiDF6D4FixedGridShard140Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard140EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 441)) at h
  exact h

theorem suzukiDF6D4FixedGridShard140EvenFull_eq_live :
    suzukiDF6D4FixedGridShard140EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 441) := by
  have h := suzukiDF6D4FixedGridShard140Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard140EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 441)) at h
  exact h

def suzukiDF6D4FixedGridShard140EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard140EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard140EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard140EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard140EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard140EvenResidualData =
      suzukiDF6D4FixedGridShard140EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard140Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard140EvenResidualData =
    suzukiDF6D4FixedGridShard140EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard140EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard140EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 441 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 441) := by
    rw [suzukiDF6D4FixedGridShard140EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 441
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140EvenDotSoundness i
          suzukiDF6D4FixedGridShard140EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 441) := by
    simpa [suzukiDF6D4FixedGridShard140EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard140EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 441) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 441) := by
    rw [suzukiDF6D4FixedGridShard140EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 441
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard140EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard140EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard140EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard140EvenDotSoundness i
            suzukiDF6D4FixedGridShard140EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard140EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard140OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard140OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 441) := by
  have h := suzukiDF6D4FixedGridShard140Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard140OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 441)) at h
  exact h

theorem suzukiDF6D4FixedGridShard140OddFull_eq_live :
    suzukiDF6D4FixedGridShard140OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 441) := by
  have h := suzukiDF6D4FixedGridShard140Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard140OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 441)) at h
  exact h

def suzukiDF6D4FixedGridShard140OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard140OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard140OddDotSoundness i.val
        suzukiDF6D4FixedGridShard140OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard140OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard140OddResidualData =
      suzukiDF6D4FixedGridShard140OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard140Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard140OddResidualData =
    suzukiDF6D4FixedGridShard140OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard140OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard140OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 441 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 441) := by
    rw [suzukiDF6D4FixedGridShard140OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 441
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140OddDotSoundness i
          suzukiDF6D4FixedGridShard140OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 441) := by
    simpa [suzukiDF6D4FixedGridShard140OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard140OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 441) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard140OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 441) := by
    rw [suzukiDF6D4FixedGridShard140OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 441
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard140OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard140OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard140OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard140OddDotSoundness i
            suzukiDF6D4FixedGridShard140OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard140OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
