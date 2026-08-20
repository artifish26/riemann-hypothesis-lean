import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard204Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard204Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard204EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard204EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 204 k) := by
  have h := suzukiDF6D4FixedGridShard204Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard204EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 204 k)) at h
  exact h

def suzukiDF6D4FixedGridShard204EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard204EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard204EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard204EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard204EvenComparisonData)

theorem suzukiDF6D4FixedGridShard204EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard204EvenSolveData =
      suzukiDF6D4FixedGridShard204EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard204Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard204EvenSolveData =
    suzukiDF6D4FixedGridShard204EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard204EvenCross_eq_live :
    suzukiDF6D4FixedGridShard204EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 204) := by
  have h := suzukiDF6D4FixedGridShard204Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard204EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 204)) at h
  exact h

theorem suzukiDF6D4FixedGridShard204EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard204EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 204 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 204 k) := by
    rw [suzukiDF6D4FixedGridShard204EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 204 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204EvenDotSoundness i
          suzukiDF6D4FixedGridShard204EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 204 k) := by
    simpa [suzukiDF6D4FixedGridShard204EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard204EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 204 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 204) := by
    rw [suzukiDF6D4FixedGridShard204EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 204)
  rw [suzukiDF6D4FixedGridShard204EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard204EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard204EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard204EvenDotSoundness i
            suzukiDF6D4FixedGridShard204EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard204EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard204OddComparison_eq_live :
    suzukiDF6D4FixedGridShard204OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 204 k) := by
  have h := suzukiDF6D4FixedGridShard204Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard204OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 204 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard204OddCross_eq_live :
    suzukiDF6D4FixedGridShard204OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 204) := by
  have h := suzukiDF6D4FixedGridShard204Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard204OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 204)) at h
  exact h

def suzukiDF6D4FixedGridShard204OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard204OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard204OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard204OddDotSoundness i.val
      suzukiDF6D4FixedGridShard204OddComparisonData)

theorem suzukiDF6D4FixedGridShard204OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard204OddSolveData =
      suzukiDF6D4FixedGridShard204OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard204Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard204OddSolveData =
    suzukiDF6D4FixedGridShard204OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard204OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard204OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 204 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 204 k) := by
    rw [suzukiDF6D4FixedGridShard204OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 204 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204OddDotSoundness i
          suzukiDF6D4FixedGridShard204OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 204 k) := by
    simpa [suzukiDF6D4FixedGridShard204OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard204OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 204 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 204) := by
    rw [suzukiDF6D4FixedGridShard204OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 204)
  rw [suzukiDF6D4FixedGridShard204OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard204OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard204OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard204OddDotSoundness i
            suzukiDF6D4FixedGridShard204OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard204OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard204EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard204EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 505) := by
  have h := suzukiDF6D4FixedGridShard204Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard204EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 505)) at h
  exact h

theorem suzukiDF6D4FixedGridShard204EvenFull_eq_live :
    suzukiDF6D4FixedGridShard204EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 505) := by
  have h := suzukiDF6D4FixedGridShard204Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard204EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 505)) at h
  exact h

def suzukiDF6D4FixedGridShard204EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard204EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard204EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard204EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard204EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard204EvenResidualData =
      suzukiDF6D4FixedGridShard204EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard204Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard204EvenResidualData =
    suzukiDF6D4FixedGridShard204EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard204EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard204EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 505 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 505) := by
    rw [suzukiDF6D4FixedGridShard204EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 505
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204EvenDotSoundness i
          suzukiDF6D4FixedGridShard204EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 505) := by
    simpa [suzukiDF6D4FixedGridShard204EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard204EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 505) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 505) := by
    rw [suzukiDF6D4FixedGridShard204EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 505
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard204EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard204EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard204EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard204EvenDotSoundness i
            suzukiDF6D4FixedGridShard204EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard204EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard204OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard204OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 505) := by
  have h := suzukiDF6D4FixedGridShard204Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard204OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 505)) at h
  exact h

theorem suzukiDF6D4FixedGridShard204OddFull_eq_live :
    suzukiDF6D4FixedGridShard204OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 505) := by
  have h := suzukiDF6D4FixedGridShard204Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard204OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 505)) at h
  exact h

def suzukiDF6D4FixedGridShard204OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard204OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard204OddDotSoundness i.val
        suzukiDF6D4FixedGridShard204OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard204OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard204OddResidualData =
      suzukiDF6D4FixedGridShard204OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard204Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard204OddResidualData =
    suzukiDF6D4FixedGridShard204OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard204OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard204OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 505 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 505) := by
    rw [suzukiDF6D4FixedGridShard204OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 505
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204OddDotSoundness i
          suzukiDF6D4FixedGridShard204OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 505) := by
    simpa [suzukiDF6D4FixedGridShard204OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard204OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 505) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard204OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 505) := by
    rw [suzukiDF6D4FixedGridShard204OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 505
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard204OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard204OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard204OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard204OddDotSoundness i
            suzukiDF6D4FixedGridShard204OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard204OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
