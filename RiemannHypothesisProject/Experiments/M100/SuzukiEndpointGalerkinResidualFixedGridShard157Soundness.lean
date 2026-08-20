import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard157Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard157Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard157EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard157EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 157 k) := by
  have h := suzukiDF6D4FixedGridShard157Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard157EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 157 k)) at h
  exact h

def suzukiDF6D4FixedGridShard157EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard157EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard157EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard157EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard157EvenComparisonData)

theorem suzukiDF6D4FixedGridShard157EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard157EvenSolveData =
      suzukiDF6D4FixedGridShard157EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard157Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard157EvenSolveData =
    suzukiDF6D4FixedGridShard157EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard157EvenCross_eq_live :
    suzukiDF6D4FixedGridShard157EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 157) := by
  have h := suzukiDF6D4FixedGridShard157Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard157EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 157)) at h
  exact h

theorem suzukiDF6D4FixedGridShard157EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard157EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 157 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 157 k) := by
    rw [suzukiDF6D4FixedGridShard157EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 157 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157EvenDotSoundness i
          suzukiDF6D4FixedGridShard157EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 157 k) := by
    simpa [suzukiDF6D4FixedGridShard157EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard157EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 157 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 157) := by
    rw [suzukiDF6D4FixedGridShard157EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 157)
  rw [suzukiDF6D4FixedGridShard157EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard157EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard157EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard157EvenDotSoundness i
            suzukiDF6D4FixedGridShard157EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard157EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard157OddComparison_eq_live :
    suzukiDF6D4FixedGridShard157OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 157 k) := by
  have h := suzukiDF6D4FixedGridShard157Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard157OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 157 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard157OddCross_eq_live :
    suzukiDF6D4FixedGridShard157OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 157) := by
  have h := suzukiDF6D4FixedGridShard157Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard157OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 157)) at h
  exact h

def suzukiDF6D4FixedGridShard157OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard157OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard157OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard157OddDotSoundness i.val
      suzukiDF6D4FixedGridShard157OddComparisonData)

theorem suzukiDF6D4FixedGridShard157OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard157OddSolveData =
      suzukiDF6D4FixedGridShard157OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard157Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard157OddSolveData =
    suzukiDF6D4FixedGridShard157OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard157OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard157OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 157 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 157 k) := by
    rw [suzukiDF6D4FixedGridShard157OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 157 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157OddDotSoundness i
          suzukiDF6D4FixedGridShard157OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 157 k) := by
    simpa [suzukiDF6D4FixedGridShard157OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard157OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 157 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 157) := by
    rw [suzukiDF6D4FixedGridShard157OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 157)
  rw [suzukiDF6D4FixedGridShard157OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard157OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard157OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard157OddDotSoundness i
            suzukiDF6D4FixedGridShard157OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard157OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard157EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard157EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 458) := by
  have h := suzukiDF6D4FixedGridShard157Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard157EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 458)) at h
  exact h

theorem suzukiDF6D4FixedGridShard157EvenFull_eq_live :
    suzukiDF6D4FixedGridShard157EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 458) := by
  have h := suzukiDF6D4FixedGridShard157Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard157EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 458)) at h
  exact h

def suzukiDF6D4FixedGridShard157EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard157EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard157EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard157EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard157EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard157EvenResidualData =
      suzukiDF6D4FixedGridShard157EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard157Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard157EvenResidualData =
    suzukiDF6D4FixedGridShard157EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard157EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard157EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 458 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 458) := by
    rw [suzukiDF6D4FixedGridShard157EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 458
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157EvenDotSoundness i
          suzukiDF6D4FixedGridShard157EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 458) := by
    simpa [suzukiDF6D4FixedGridShard157EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard157EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 458) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 458) := by
    rw [suzukiDF6D4FixedGridShard157EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 458
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard157EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard157EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard157EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard157EvenDotSoundness i
            suzukiDF6D4FixedGridShard157EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard157EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard157OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard157OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 458) := by
  have h := suzukiDF6D4FixedGridShard157Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard157OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 458)) at h
  exact h

theorem suzukiDF6D4FixedGridShard157OddFull_eq_live :
    suzukiDF6D4FixedGridShard157OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 458) := by
  have h := suzukiDF6D4FixedGridShard157Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard157OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 458)) at h
  exact h

def suzukiDF6D4FixedGridShard157OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard157OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard157OddDotSoundness i.val
        suzukiDF6D4FixedGridShard157OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard157OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard157OddResidualData =
      suzukiDF6D4FixedGridShard157OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard157Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard157OddResidualData =
    suzukiDF6D4FixedGridShard157OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard157OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard157OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 458 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 458) := by
    rw [suzukiDF6D4FixedGridShard157OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 458
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157OddDotSoundness i
          suzukiDF6D4FixedGridShard157OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 458) := by
    simpa [suzukiDF6D4FixedGridShard157OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard157OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 458) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard157OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 458) := by
    rw [suzukiDF6D4FixedGridShard157OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 458
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard157OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard157OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard157OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard157OddDotSoundness i
            suzukiDF6D4FixedGridShard157OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard157OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
