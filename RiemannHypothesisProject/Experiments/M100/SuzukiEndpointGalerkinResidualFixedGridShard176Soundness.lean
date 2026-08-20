import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard176Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard176Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard176EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard176EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 176 k) := by
  have h := suzukiDF6D4FixedGridShard176Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard176EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 176 k)) at h
  exact h

def suzukiDF6D4FixedGridShard176EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard176EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard176EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard176EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard176EvenComparisonData)

theorem suzukiDF6D4FixedGridShard176EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard176EvenSolveData =
      suzukiDF6D4FixedGridShard176EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard176Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard176EvenSolveData =
    suzukiDF6D4FixedGridShard176EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard176EvenCross_eq_live :
    suzukiDF6D4FixedGridShard176EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 176) := by
  have h := suzukiDF6D4FixedGridShard176Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard176EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 176)) at h
  exact h

theorem suzukiDF6D4FixedGridShard176EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard176EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 176 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 176 k) := by
    rw [suzukiDF6D4FixedGridShard176EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 176 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176EvenDotSoundness i
          suzukiDF6D4FixedGridShard176EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 176 k) := by
    simpa [suzukiDF6D4FixedGridShard176EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard176EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 176 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 176) := by
    rw [suzukiDF6D4FixedGridShard176EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 176)
  rw [suzukiDF6D4FixedGridShard176EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard176EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard176EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard176EvenDotSoundness i
            suzukiDF6D4FixedGridShard176EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard176EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard176OddComparison_eq_live :
    suzukiDF6D4FixedGridShard176OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 176 k) := by
  have h := suzukiDF6D4FixedGridShard176Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard176OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 176 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard176OddCross_eq_live :
    suzukiDF6D4FixedGridShard176OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 176) := by
  have h := suzukiDF6D4FixedGridShard176Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard176OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 176)) at h
  exact h

def suzukiDF6D4FixedGridShard176OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard176OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard176OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard176OddDotSoundness i.val
      suzukiDF6D4FixedGridShard176OddComparisonData)

theorem suzukiDF6D4FixedGridShard176OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard176OddSolveData =
      suzukiDF6D4FixedGridShard176OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard176Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard176OddSolveData =
    suzukiDF6D4FixedGridShard176OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard176OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard176OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 176 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 176 k) := by
    rw [suzukiDF6D4FixedGridShard176OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 176 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176OddDotSoundness i
          suzukiDF6D4FixedGridShard176OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 176 k) := by
    simpa [suzukiDF6D4FixedGridShard176OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard176OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 176 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 176) := by
    rw [suzukiDF6D4FixedGridShard176OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 176)
  rw [suzukiDF6D4FixedGridShard176OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard176OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard176OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard176OddDotSoundness i
            suzukiDF6D4FixedGridShard176OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard176OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard176EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard176EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 477) := by
  have h := suzukiDF6D4FixedGridShard176Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard176EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 477)) at h
  exact h

theorem suzukiDF6D4FixedGridShard176EvenFull_eq_live :
    suzukiDF6D4FixedGridShard176EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 477) := by
  have h := suzukiDF6D4FixedGridShard176Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard176EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 477)) at h
  exact h

def suzukiDF6D4FixedGridShard176EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard176EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard176EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard176EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard176EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard176EvenResidualData =
      suzukiDF6D4FixedGridShard176EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard176Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard176EvenResidualData =
    suzukiDF6D4FixedGridShard176EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard176EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard176EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 477 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 477) := by
    rw [suzukiDF6D4FixedGridShard176EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 477
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176EvenDotSoundness i
          suzukiDF6D4FixedGridShard176EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 477) := by
    simpa [suzukiDF6D4FixedGridShard176EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard176EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 477) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 477) := by
    rw [suzukiDF6D4FixedGridShard176EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 477
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard176EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard176EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard176EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard176EvenDotSoundness i
            suzukiDF6D4FixedGridShard176EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard176EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard176OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard176OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 477) := by
  have h := suzukiDF6D4FixedGridShard176Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard176OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 477)) at h
  exact h

theorem suzukiDF6D4FixedGridShard176OddFull_eq_live :
    suzukiDF6D4FixedGridShard176OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 477) := by
  have h := suzukiDF6D4FixedGridShard176Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard176OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 477)) at h
  exact h

def suzukiDF6D4FixedGridShard176OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard176OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard176OddDotSoundness i.val
        suzukiDF6D4FixedGridShard176OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard176OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard176OddResidualData =
      suzukiDF6D4FixedGridShard176OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard176Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard176OddResidualData =
    suzukiDF6D4FixedGridShard176OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard176OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard176OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 477 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 477) := by
    rw [suzukiDF6D4FixedGridShard176OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 477
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176OddDotSoundness i
          suzukiDF6D4FixedGridShard176OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 477) := by
    simpa [suzukiDF6D4FixedGridShard176OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard176OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 477) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard176OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 477) := by
    rw [suzukiDF6D4FixedGridShard176OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 477
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard176OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard176OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard176OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard176OddDotSoundness i
            suzukiDF6D4FixedGridShard176OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard176OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
