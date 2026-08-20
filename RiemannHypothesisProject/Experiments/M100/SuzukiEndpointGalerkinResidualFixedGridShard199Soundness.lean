import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard199Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard199Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard199EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard199EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 199 k) := by
  have h := suzukiDF6D4FixedGridShard199Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard199EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 199 k)) at h
  exact h

def suzukiDF6D4FixedGridShard199EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard199EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard199EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard199EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard199EvenComparisonData)

theorem suzukiDF6D4FixedGridShard199EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard199EvenSolveData =
      suzukiDF6D4FixedGridShard199EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard199Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard199EvenSolveData =
    suzukiDF6D4FixedGridShard199EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard199EvenCross_eq_live :
    suzukiDF6D4FixedGridShard199EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 199) := by
  have h := suzukiDF6D4FixedGridShard199Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard199EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 199)) at h
  exact h

theorem suzukiDF6D4FixedGridShard199EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard199EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 199 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 199 k) := by
    rw [suzukiDF6D4FixedGridShard199EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 199 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199EvenDotSoundness i
          suzukiDF6D4FixedGridShard199EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 199 k) := by
    simpa [suzukiDF6D4FixedGridShard199EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard199EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 199 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 199) := by
    rw [suzukiDF6D4FixedGridShard199EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 199)
  rw [suzukiDF6D4FixedGridShard199EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard199EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard199EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard199EvenDotSoundness i
            suzukiDF6D4FixedGridShard199EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard199EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard199OddComparison_eq_live :
    suzukiDF6D4FixedGridShard199OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 199 k) := by
  have h := suzukiDF6D4FixedGridShard199Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard199OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 199 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard199OddCross_eq_live :
    suzukiDF6D4FixedGridShard199OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 199) := by
  have h := suzukiDF6D4FixedGridShard199Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard199OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 199)) at h
  exact h

def suzukiDF6D4FixedGridShard199OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard199OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard199OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard199OddDotSoundness i.val
      suzukiDF6D4FixedGridShard199OddComparisonData)

theorem suzukiDF6D4FixedGridShard199OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard199OddSolveData =
      suzukiDF6D4FixedGridShard199OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard199Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard199OddSolveData =
    suzukiDF6D4FixedGridShard199OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard199OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard199OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 199 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 199 k) := by
    rw [suzukiDF6D4FixedGridShard199OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 199 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199OddDotSoundness i
          suzukiDF6D4FixedGridShard199OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 199 k) := by
    simpa [suzukiDF6D4FixedGridShard199OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard199OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 199 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 199) := by
    rw [suzukiDF6D4FixedGridShard199OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 199)
  rw [suzukiDF6D4FixedGridShard199OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard199OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard199OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard199OddDotSoundness i
            suzukiDF6D4FixedGridShard199OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard199OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard199EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard199EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 500) := by
  have h := suzukiDF6D4FixedGridShard199Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard199EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 500)) at h
  exact h

theorem suzukiDF6D4FixedGridShard199EvenFull_eq_live :
    suzukiDF6D4FixedGridShard199EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 500) := by
  have h := suzukiDF6D4FixedGridShard199Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard199EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 500)) at h
  exact h

def suzukiDF6D4FixedGridShard199EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard199EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard199EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard199EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard199EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard199EvenResidualData =
      suzukiDF6D4FixedGridShard199EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard199Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard199EvenResidualData =
    suzukiDF6D4FixedGridShard199EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard199EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard199EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 500 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 500) := by
    rw [suzukiDF6D4FixedGridShard199EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 500
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199EvenDotSoundness i
          suzukiDF6D4FixedGridShard199EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 500) := by
    simpa [suzukiDF6D4FixedGridShard199EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard199EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 500) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 500) := by
    rw [suzukiDF6D4FixedGridShard199EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 500
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard199EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard199EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard199EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard199EvenDotSoundness i
            suzukiDF6D4FixedGridShard199EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard199EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard199OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard199OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 500) := by
  have h := suzukiDF6D4FixedGridShard199Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard199OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 500)) at h
  exact h

theorem suzukiDF6D4FixedGridShard199OddFull_eq_live :
    suzukiDF6D4FixedGridShard199OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 500) := by
  have h := suzukiDF6D4FixedGridShard199Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard199OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 500)) at h
  exact h

def suzukiDF6D4FixedGridShard199OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard199OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard199OddDotSoundness i.val
        suzukiDF6D4FixedGridShard199OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard199OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard199OddResidualData =
      suzukiDF6D4FixedGridShard199OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard199Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard199OddResidualData =
    suzukiDF6D4FixedGridShard199OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard199OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard199OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 500 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 500) := by
    rw [suzukiDF6D4FixedGridShard199OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 500
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199OddDotSoundness i
          suzukiDF6D4FixedGridShard199OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 500) := by
    simpa [suzukiDF6D4FixedGridShard199OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard199OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 500) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard199OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 500) := by
    rw [suzukiDF6D4FixedGridShard199OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 500
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard199OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard199OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard199OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard199OddDotSoundness i
            suzukiDF6D4FixedGridShard199OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard199OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
