import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard107Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard107Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard107EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard107EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 107 k) := by
  have h := suzukiDF6D4FixedGridShard107Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard107EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 107 k)) at h
  exact h

def suzukiDF6D4FixedGridShard107EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard107EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard107EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard107EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard107EvenComparisonData)

theorem suzukiDF6D4FixedGridShard107EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard107EvenSolveData =
      suzukiDF6D4FixedGridShard107EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard107Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard107EvenSolveData =
    suzukiDF6D4FixedGridShard107EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard107EvenCross_eq_live :
    suzukiDF6D4FixedGridShard107EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 107) := by
  have h := suzukiDF6D4FixedGridShard107Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard107EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 107)) at h
  exact h

theorem suzukiDF6D4FixedGridShard107EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard107EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 107 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 107 k) := by
    rw [suzukiDF6D4FixedGridShard107EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 107 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107EvenDotSoundness i
          suzukiDF6D4FixedGridShard107EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 107 k) := by
    simpa [suzukiDF6D4FixedGridShard107EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard107EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 107 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 107) := by
    rw [suzukiDF6D4FixedGridShard107EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 107)
  rw [suzukiDF6D4FixedGridShard107EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard107EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard107EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard107EvenDotSoundness i
            suzukiDF6D4FixedGridShard107EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard107EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard107OddComparison_eq_live :
    suzukiDF6D4FixedGridShard107OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 107 k) := by
  have h := suzukiDF6D4FixedGridShard107Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard107OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 107 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard107OddCross_eq_live :
    suzukiDF6D4FixedGridShard107OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 107) := by
  have h := suzukiDF6D4FixedGridShard107Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard107OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 107)) at h
  exact h

def suzukiDF6D4FixedGridShard107OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard107OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard107OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard107OddDotSoundness i.val
      suzukiDF6D4FixedGridShard107OddComparisonData)

theorem suzukiDF6D4FixedGridShard107OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard107OddSolveData =
      suzukiDF6D4FixedGridShard107OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard107Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard107OddSolveData =
    suzukiDF6D4FixedGridShard107OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard107OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard107OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 107 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 107 k) := by
    rw [suzukiDF6D4FixedGridShard107OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 107 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107OddDotSoundness i
          suzukiDF6D4FixedGridShard107OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 107 k) := by
    simpa [suzukiDF6D4FixedGridShard107OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard107OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 107 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 107) := by
    rw [suzukiDF6D4FixedGridShard107OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 107)
  rw [suzukiDF6D4FixedGridShard107OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard107OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard107OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard107OddDotSoundness i
            suzukiDF6D4FixedGridShard107OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard107OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard107EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard107EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 408) := by
  have h := suzukiDF6D4FixedGridShard107Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard107EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 408)) at h
  exact h

theorem suzukiDF6D4FixedGridShard107EvenFull_eq_live :
    suzukiDF6D4FixedGridShard107EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 408) := by
  have h := suzukiDF6D4FixedGridShard107Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard107EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 408)) at h
  exact h

def suzukiDF6D4FixedGridShard107EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard107EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard107EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard107EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard107EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard107EvenResidualData =
      suzukiDF6D4FixedGridShard107EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard107Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard107EvenResidualData =
    suzukiDF6D4FixedGridShard107EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard107EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard107EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 408 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 408) := by
    rw [suzukiDF6D4FixedGridShard107EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 408
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107EvenDotSoundness i
          suzukiDF6D4FixedGridShard107EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 408) := by
    simpa [suzukiDF6D4FixedGridShard107EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard107EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 408) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 408) := by
    rw [suzukiDF6D4FixedGridShard107EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 408
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard107EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard107EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard107EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard107EvenDotSoundness i
            suzukiDF6D4FixedGridShard107EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard107EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard107OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard107OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 408) := by
  have h := suzukiDF6D4FixedGridShard107Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard107OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 408)) at h
  exact h

theorem suzukiDF6D4FixedGridShard107OddFull_eq_live :
    suzukiDF6D4FixedGridShard107OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 408) := by
  have h := suzukiDF6D4FixedGridShard107Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard107OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 408)) at h
  exact h

def suzukiDF6D4FixedGridShard107OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard107OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard107OddDotSoundness i.val
        suzukiDF6D4FixedGridShard107OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard107OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard107OddResidualData =
      suzukiDF6D4FixedGridShard107OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard107Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard107OddResidualData =
    suzukiDF6D4FixedGridShard107OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard107OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard107OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 408 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 408) := by
    rw [suzukiDF6D4FixedGridShard107OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 408
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107OddDotSoundness i
          suzukiDF6D4FixedGridShard107OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 408) := by
    simpa [suzukiDF6D4FixedGridShard107OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard107OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 408) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard107OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 408) := by
    rw [suzukiDF6D4FixedGridShard107OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 408
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard107OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard107OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard107OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard107OddDotSoundness i
            suzukiDF6D4FixedGridShard107OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard107OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
