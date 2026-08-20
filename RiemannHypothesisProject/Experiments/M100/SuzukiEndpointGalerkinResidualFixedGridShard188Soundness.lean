import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard188Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard188Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard188EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard188EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 188 k) := by
  have h := suzukiDF6D4FixedGridShard188Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard188EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 188 k)) at h
  exact h

def suzukiDF6D4FixedGridShard188EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard188EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard188EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard188EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard188EvenComparisonData)

theorem suzukiDF6D4FixedGridShard188EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard188EvenSolveData =
      suzukiDF6D4FixedGridShard188EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard188Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard188EvenSolveData =
    suzukiDF6D4FixedGridShard188EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard188EvenCross_eq_live :
    suzukiDF6D4FixedGridShard188EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 188) := by
  have h := suzukiDF6D4FixedGridShard188Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard188EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 188)) at h
  exact h

theorem suzukiDF6D4FixedGridShard188EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard188EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 188 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 188 k) := by
    rw [suzukiDF6D4FixedGridShard188EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 188 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188EvenDotSoundness i
          suzukiDF6D4FixedGridShard188EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 188 k) := by
    simpa [suzukiDF6D4FixedGridShard188EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard188EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 188 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 188) := by
    rw [suzukiDF6D4FixedGridShard188EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 188)
  rw [suzukiDF6D4FixedGridShard188EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard188EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard188EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard188EvenDotSoundness i
            suzukiDF6D4FixedGridShard188EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard188EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard188OddComparison_eq_live :
    suzukiDF6D4FixedGridShard188OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 188 k) := by
  have h := suzukiDF6D4FixedGridShard188Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard188OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 188 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard188OddCross_eq_live :
    suzukiDF6D4FixedGridShard188OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 188) := by
  have h := suzukiDF6D4FixedGridShard188Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard188OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 188)) at h
  exact h

def suzukiDF6D4FixedGridShard188OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard188OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard188OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard188OddDotSoundness i.val
      suzukiDF6D4FixedGridShard188OddComparisonData)

theorem suzukiDF6D4FixedGridShard188OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard188OddSolveData =
      suzukiDF6D4FixedGridShard188OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard188Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard188OddSolveData =
    suzukiDF6D4FixedGridShard188OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard188OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard188OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 188 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 188 k) := by
    rw [suzukiDF6D4FixedGridShard188OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 188 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188OddDotSoundness i
          suzukiDF6D4FixedGridShard188OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 188 k) := by
    simpa [suzukiDF6D4FixedGridShard188OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard188OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 188 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 188) := by
    rw [suzukiDF6D4FixedGridShard188OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 188)
  rw [suzukiDF6D4FixedGridShard188OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard188OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard188OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard188OddDotSoundness i
            suzukiDF6D4FixedGridShard188OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard188OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard188EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard188EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 489) := by
  have h := suzukiDF6D4FixedGridShard188Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard188EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 489)) at h
  exact h

theorem suzukiDF6D4FixedGridShard188EvenFull_eq_live :
    suzukiDF6D4FixedGridShard188EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 489) := by
  have h := suzukiDF6D4FixedGridShard188Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard188EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 489)) at h
  exact h

def suzukiDF6D4FixedGridShard188EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard188EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard188EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard188EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard188EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard188EvenResidualData =
      suzukiDF6D4FixedGridShard188EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard188Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard188EvenResidualData =
    suzukiDF6D4FixedGridShard188EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard188EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard188EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 489 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 489) := by
    rw [suzukiDF6D4FixedGridShard188EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 489
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188EvenDotSoundness i
          suzukiDF6D4FixedGridShard188EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 489) := by
    simpa [suzukiDF6D4FixedGridShard188EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard188EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 489) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 489) := by
    rw [suzukiDF6D4FixedGridShard188EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 489
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard188EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard188EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard188EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard188EvenDotSoundness i
            suzukiDF6D4FixedGridShard188EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard188EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard188OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard188OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 489) := by
  have h := suzukiDF6D4FixedGridShard188Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard188OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 489)) at h
  exact h

theorem suzukiDF6D4FixedGridShard188OddFull_eq_live :
    suzukiDF6D4FixedGridShard188OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 489) := by
  have h := suzukiDF6D4FixedGridShard188Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard188OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 489)) at h
  exact h

def suzukiDF6D4FixedGridShard188OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard188OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard188OddDotSoundness i.val
        suzukiDF6D4FixedGridShard188OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard188OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard188OddResidualData =
      suzukiDF6D4FixedGridShard188OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard188Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard188OddResidualData =
    suzukiDF6D4FixedGridShard188OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard188OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard188OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 489 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 489) := by
    rw [suzukiDF6D4FixedGridShard188OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 489
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188OddDotSoundness i
          suzukiDF6D4FixedGridShard188OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 489) := by
    simpa [suzukiDF6D4FixedGridShard188OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard188OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 489) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard188OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 489) := by
    rw [suzukiDF6D4FixedGridShard188OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 489
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard188OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard188OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard188OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard188OddDotSoundness i
            suzukiDF6D4FixedGridShard188OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard188OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
