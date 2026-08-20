import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard029Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard029Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard029EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard029EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 29 k) := by
  have h := suzukiDF6D4FixedGridShard029Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard029EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 29 k)) at h
  exact h

def suzukiDF6D4FixedGridShard029EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard029EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard029EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard029EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard029EvenComparisonData)

theorem suzukiDF6D4FixedGridShard029EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard029EvenSolveData =
      suzukiDF6D4FixedGridShard029EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard029Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard029EvenSolveData =
    suzukiDF6D4FixedGridShard029EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard029EvenCross_eq_live :
    suzukiDF6D4FixedGridShard029EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 29) := by
  have h := suzukiDF6D4FixedGridShard029Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard029EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 29)) at h
  exact h

theorem suzukiDF6D4FixedGridShard029EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard029EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 29 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 29 k) := by
    rw [suzukiDF6D4FixedGridShard029EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 29 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029EvenDotSoundness i
          suzukiDF6D4FixedGridShard029EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 29 k) := by
    simpa [suzukiDF6D4FixedGridShard029EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard029EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 29 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 29) := by
    rw [suzukiDF6D4FixedGridShard029EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 29)
  rw [suzukiDF6D4FixedGridShard029EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard029EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard029EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard029EvenDotSoundness i
            suzukiDF6D4FixedGridShard029EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard029EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard029OddComparison_eq_live :
    suzukiDF6D4FixedGridShard029OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 29 k) := by
  have h := suzukiDF6D4FixedGridShard029Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard029OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 29 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard029OddCross_eq_live :
    suzukiDF6D4FixedGridShard029OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 29) := by
  have h := suzukiDF6D4FixedGridShard029Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard029OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 29)) at h
  exact h

def suzukiDF6D4FixedGridShard029OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard029OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard029OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard029OddDotSoundness i.val
      suzukiDF6D4FixedGridShard029OddComparisonData)

theorem suzukiDF6D4FixedGridShard029OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard029OddSolveData =
      suzukiDF6D4FixedGridShard029OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard029Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard029OddSolveData =
    suzukiDF6D4FixedGridShard029OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard029OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard029OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 29 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 29 k) := by
    rw [suzukiDF6D4FixedGridShard029OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 29 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029OddDotSoundness i
          suzukiDF6D4FixedGridShard029OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 29 k) := by
    simpa [suzukiDF6D4FixedGridShard029OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard029OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 29 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 29) := by
    rw [suzukiDF6D4FixedGridShard029OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 29)
  rw [suzukiDF6D4FixedGridShard029OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard029OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard029OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard029OddDotSoundness i
            suzukiDF6D4FixedGridShard029OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard029OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard029EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard029EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 330) := by
  have h := suzukiDF6D4FixedGridShard029Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard029EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 330)) at h
  exact h

theorem suzukiDF6D4FixedGridShard029EvenFull_eq_live :
    suzukiDF6D4FixedGridShard029EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 330) := by
  have h := suzukiDF6D4FixedGridShard029Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard029EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 330)) at h
  exact h

def suzukiDF6D4FixedGridShard029EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard029EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard029EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard029EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard029EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard029EvenResidualData =
      suzukiDF6D4FixedGridShard029EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard029Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard029EvenResidualData =
    suzukiDF6D4FixedGridShard029EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard029EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard029EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 330 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 330) := by
    rw [suzukiDF6D4FixedGridShard029EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 330
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029EvenDotSoundness i
          suzukiDF6D4FixedGridShard029EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 330) := by
    simpa [suzukiDF6D4FixedGridShard029EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard029EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 330) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 330) := by
    rw [suzukiDF6D4FixedGridShard029EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 330
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard029EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard029EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard029EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard029EvenDotSoundness i
            suzukiDF6D4FixedGridShard029EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard029EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard029OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard029OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 330) := by
  have h := suzukiDF6D4FixedGridShard029Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard029OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 330)) at h
  exact h

theorem suzukiDF6D4FixedGridShard029OddFull_eq_live :
    suzukiDF6D4FixedGridShard029OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 330) := by
  have h := suzukiDF6D4FixedGridShard029Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard029OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 330)) at h
  exact h

def suzukiDF6D4FixedGridShard029OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard029OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard029OddDotSoundness i.val
        suzukiDF6D4FixedGridShard029OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard029OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard029OddResidualData =
      suzukiDF6D4FixedGridShard029OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard029Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard029OddResidualData =
    suzukiDF6D4FixedGridShard029OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard029OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard029OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 330 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 330) := by
    rw [suzukiDF6D4FixedGridShard029OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 330
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029OddDotSoundness i
          suzukiDF6D4FixedGridShard029OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 330) := by
    simpa [suzukiDF6D4FixedGridShard029OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard029OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 330) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard029OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 330) := by
    rw [suzukiDF6D4FixedGridShard029OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 330
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard029OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard029OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard029OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard029OddDotSoundness i
            suzukiDF6D4FixedGridShard029OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard029OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
