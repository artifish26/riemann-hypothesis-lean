import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard130Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard130Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard130EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard130EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 130 k) := by
  have h := suzukiDF6D4FixedGridShard130Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard130EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 130 k)) at h
  exact h

def suzukiDF6D4FixedGridShard130EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard130EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard130EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard130EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard130EvenComparisonData)

theorem suzukiDF6D4FixedGridShard130EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard130EvenSolveData =
      suzukiDF6D4FixedGridShard130EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard130Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard130EvenSolveData =
    suzukiDF6D4FixedGridShard130EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard130EvenCross_eq_live :
    suzukiDF6D4FixedGridShard130EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 130) := by
  have h := suzukiDF6D4FixedGridShard130Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard130EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 130)) at h
  exact h

theorem suzukiDF6D4FixedGridShard130EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard130EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 130 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 130 k) := by
    rw [suzukiDF6D4FixedGridShard130EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 130 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130EvenDotSoundness i
          suzukiDF6D4FixedGridShard130EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 130 k) := by
    simpa [suzukiDF6D4FixedGridShard130EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard130EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 130 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 130) := by
    rw [suzukiDF6D4FixedGridShard130EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 130)
  rw [suzukiDF6D4FixedGridShard130EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard130EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard130EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard130EvenDotSoundness i
            suzukiDF6D4FixedGridShard130EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard130EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard130OddComparison_eq_live :
    suzukiDF6D4FixedGridShard130OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 130 k) := by
  have h := suzukiDF6D4FixedGridShard130Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard130OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 130 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard130OddCross_eq_live :
    suzukiDF6D4FixedGridShard130OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 130) := by
  have h := suzukiDF6D4FixedGridShard130Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard130OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 130)) at h
  exact h

def suzukiDF6D4FixedGridShard130OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard130OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard130OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard130OddDotSoundness i.val
      suzukiDF6D4FixedGridShard130OddComparisonData)

theorem suzukiDF6D4FixedGridShard130OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard130OddSolveData =
      suzukiDF6D4FixedGridShard130OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard130Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard130OddSolveData =
    suzukiDF6D4FixedGridShard130OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard130OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard130OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 130 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 130 k) := by
    rw [suzukiDF6D4FixedGridShard130OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 130 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130OddDotSoundness i
          suzukiDF6D4FixedGridShard130OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 130 k) := by
    simpa [suzukiDF6D4FixedGridShard130OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard130OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 130 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 130) := by
    rw [suzukiDF6D4FixedGridShard130OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 130)
  rw [suzukiDF6D4FixedGridShard130OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard130OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard130OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard130OddDotSoundness i
            suzukiDF6D4FixedGridShard130OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard130OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard130EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard130EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 431) := by
  have h := suzukiDF6D4FixedGridShard130Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard130EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 431)) at h
  exact h

theorem suzukiDF6D4FixedGridShard130EvenFull_eq_live :
    suzukiDF6D4FixedGridShard130EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 431) := by
  have h := suzukiDF6D4FixedGridShard130Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard130EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 431)) at h
  exact h

def suzukiDF6D4FixedGridShard130EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard130EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard130EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard130EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard130EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard130EvenResidualData =
      suzukiDF6D4FixedGridShard130EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard130Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard130EvenResidualData =
    suzukiDF6D4FixedGridShard130EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard130EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard130EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 431 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 431) := by
    rw [suzukiDF6D4FixedGridShard130EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 431
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130EvenDotSoundness i
          suzukiDF6D4FixedGridShard130EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 431) := by
    simpa [suzukiDF6D4FixedGridShard130EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard130EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 431) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 431) := by
    rw [suzukiDF6D4FixedGridShard130EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 431
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard130EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard130EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard130EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard130EvenDotSoundness i
            suzukiDF6D4FixedGridShard130EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard130EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard130OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard130OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 431) := by
  have h := suzukiDF6D4FixedGridShard130Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard130OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 431)) at h
  exact h

theorem suzukiDF6D4FixedGridShard130OddFull_eq_live :
    suzukiDF6D4FixedGridShard130OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 431) := by
  have h := suzukiDF6D4FixedGridShard130Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard130OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 431)) at h
  exact h

def suzukiDF6D4FixedGridShard130OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard130OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard130OddDotSoundness i.val
        suzukiDF6D4FixedGridShard130OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard130OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard130OddResidualData =
      suzukiDF6D4FixedGridShard130OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard130Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard130OddResidualData =
    suzukiDF6D4FixedGridShard130OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard130OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard130OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 431 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 431) := by
    rw [suzukiDF6D4FixedGridShard130OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 431
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130OddDotSoundness i
          suzukiDF6D4FixedGridShard130OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 431) := by
    simpa [suzukiDF6D4FixedGridShard130OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard130OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 431) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard130OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 431) := by
    rw [suzukiDF6D4FixedGridShard130OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 431
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard130OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard130OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard130OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard130OddDotSoundness i
            suzukiDF6D4FixedGridShard130OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard130OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
