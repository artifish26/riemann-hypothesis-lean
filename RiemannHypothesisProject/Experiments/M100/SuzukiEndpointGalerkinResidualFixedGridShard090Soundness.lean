import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard090Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard090Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard090EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard090EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 90 k) := by
  have h := suzukiDF6D4FixedGridShard090Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard090EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 90 k)) at h
  exact h

def suzukiDF6D4FixedGridShard090EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard090EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard090EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard090EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard090EvenComparisonData)

theorem suzukiDF6D4FixedGridShard090EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard090EvenSolveData =
      suzukiDF6D4FixedGridShard090EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard090Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard090EvenSolveData =
    suzukiDF6D4FixedGridShard090EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard090EvenCross_eq_live :
    suzukiDF6D4FixedGridShard090EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 90) := by
  have h := suzukiDF6D4FixedGridShard090Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard090EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 90)) at h
  exact h

theorem suzukiDF6D4FixedGridShard090EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard090EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 90 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 90 k) := by
    rw [suzukiDF6D4FixedGridShard090EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 90 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090EvenDotSoundness i
          suzukiDF6D4FixedGridShard090EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 90 k) := by
    simpa [suzukiDF6D4FixedGridShard090EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard090EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 90 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 90) := by
    rw [suzukiDF6D4FixedGridShard090EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 90)
  rw [suzukiDF6D4FixedGridShard090EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard090EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard090EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard090EvenDotSoundness i
            suzukiDF6D4FixedGridShard090EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard090EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard090OddComparison_eq_live :
    suzukiDF6D4FixedGridShard090OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 90 k) := by
  have h := suzukiDF6D4FixedGridShard090Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard090OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 90 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard090OddCross_eq_live :
    suzukiDF6D4FixedGridShard090OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 90) := by
  have h := suzukiDF6D4FixedGridShard090Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard090OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 90)) at h
  exact h

def suzukiDF6D4FixedGridShard090OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard090OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard090OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard090OddDotSoundness i.val
      suzukiDF6D4FixedGridShard090OddComparisonData)

theorem suzukiDF6D4FixedGridShard090OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard090OddSolveData =
      suzukiDF6D4FixedGridShard090OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard090Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard090OddSolveData =
    suzukiDF6D4FixedGridShard090OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard090OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard090OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 90 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 90 k) := by
    rw [suzukiDF6D4FixedGridShard090OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 90 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090OddDotSoundness i
          suzukiDF6D4FixedGridShard090OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 90 k) := by
    simpa [suzukiDF6D4FixedGridShard090OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard090OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 90 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 90) := by
    rw [suzukiDF6D4FixedGridShard090OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 90)
  rw [suzukiDF6D4FixedGridShard090OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard090OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard090OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard090OddDotSoundness i
            suzukiDF6D4FixedGridShard090OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard090OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard090EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard090EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 391) := by
  have h := suzukiDF6D4FixedGridShard090Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard090EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 391)) at h
  exact h

theorem suzukiDF6D4FixedGridShard090EvenFull_eq_live :
    suzukiDF6D4FixedGridShard090EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 391) := by
  have h := suzukiDF6D4FixedGridShard090Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard090EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 391)) at h
  exact h

def suzukiDF6D4FixedGridShard090EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard090EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard090EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard090EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard090EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard090EvenResidualData =
      suzukiDF6D4FixedGridShard090EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard090Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard090EvenResidualData =
    suzukiDF6D4FixedGridShard090EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard090EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard090EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 391 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 391) := by
    rw [suzukiDF6D4FixedGridShard090EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 391
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090EvenDotSoundness i
          suzukiDF6D4FixedGridShard090EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 391) := by
    simpa [suzukiDF6D4FixedGridShard090EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard090EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 391) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 391) := by
    rw [suzukiDF6D4FixedGridShard090EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 391
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard090EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard090EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard090EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard090EvenDotSoundness i
            suzukiDF6D4FixedGridShard090EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard090EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard090OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard090OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 391) := by
  have h := suzukiDF6D4FixedGridShard090Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard090OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 391)) at h
  exact h

theorem suzukiDF6D4FixedGridShard090OddFull_eq_live :
    suzukiDF6D4FixedGridShard090OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 391) := by
  have h := suzukiDF6D4FixedGridShard090Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard090OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 391)) at h
  exact h

def suzukiDF6D4FixedGridShard090OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard090OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard090OddDotSoundness i.val
        suzukiDF6D4FixedGridShard090OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard090OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard090OddResidualData =
      suzukiDF6D4FixedGridShard090OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard090Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard090OddResidualData =
    suzukiDF6D4FixedGridShard090OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard090OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard090OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 391 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 391) := by
    rw [suzukiDF6D4FixedGridShard090OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 391
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090OddDotSoundness i
          suzukiDF6D4FixedGridShard090OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 391) := by
    simpa [suzukiDF6D4FixedGridShard090OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard090OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 391) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard090OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 391) := by
    rw [suzukiDF6D4FixedGridShard090OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 391
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard090OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard090OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard090OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard090OddDotSoundness i
            suzukiDF6D4FixedGridShard090OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard090OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
