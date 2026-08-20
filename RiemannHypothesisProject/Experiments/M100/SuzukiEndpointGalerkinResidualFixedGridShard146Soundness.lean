import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard146Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard146Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard146EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard146EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 146 k) := by
  have h := suzukiDF6D4FixedGridShard146Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard146EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 146 k)) at h
  exact h

def suzukiDF6D4FixedGridShard146EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard146EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard146EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard146EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard146EvenComparisonData)

theorem suzukiDF6D4FixedGridShard146EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard146EvenSolveData =
      suzukiDF6D4FixedGridShard146EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard146Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard146EvenSolveData =
    suzukiDF6D4FixedGridShard146EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard146EvenCross_eq_live :
    suzukiDF6D4FixedGridShard146EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 146) := by
  have h := suzukiDF6D4FixedGridShard146Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard146EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 146)) at h
  exact h

theorem suzukiDF6D4FixedGridShard146EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard146EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 146 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 146 k) := by
    rw [suzukiDF6D4FixedGridShard146EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 146 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146EvenDotSoundness i
          suzukiDF6D4FixedGridShard146EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 146 k) := by
    simpa [suzukiDF6D4FixedGridShard146EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard146EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 146 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 146) := by
    rw [suzukiDF6D4FixedGridShard146EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 146)
  rw [suzukiDF6D4FixedGridShard146EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard146EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard146EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard146EvenDotSoundness i
            suzukiDF6D4FixedGridShard146EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard146EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard146OddComparison_eq_live :
    suzukiDF6D4FixedGridShard146OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 146 k) := by
  have h := suzukiDF6D4FixedGridShard146Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard146OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 146 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard146OddCross_eq_live :
    suzukiDF6D4FixedGridShard146OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 146) := by
  have h := suzukiDF6D4FixedGridShard146Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard146OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 146)) at h
  exact h

def suzukiDF6D4FixedGridShard146OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard146OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard146OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard146OddDotSoundness i.val
      suzukiDF6D4FixedGridShard146OddComparisonData)

theorem suzukiDF6D4FixedGridShard146OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard146OddSolveData =
      suzukiDF6D4FixedGridShard146OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard146Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard146OddSolveData =
    suzukiDF6D4FixedGridShard146OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard146OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard146OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 146 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 146 k) := by
    rw [suzukiDF6D4FixedGridShard146OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 146 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146OddDotSoundness i
          suzukiDF6D4FixedGridShard146OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 146 k) := by
    simpa [suzukiDF6D4FixedGridShard146OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard146OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 146 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 146) := by
    rw [suzukiDF6D4FixedGridShard146OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 146)
  rw [suzukiDF6D4FixedGridShard146OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard146OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard146OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard146OddDotSoundness i
            suzukiDF6D4FixedGridShard146OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard146OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard146EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard146EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 447) := by
  have h := suzukiDF6D4FixedGridShard146Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard146EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 447)) at h
  exact h

theorem suzukiDF6D4FixedGridShard146EvenFull_eq_live :
    suzukiDF6D4FixedGridShard146EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 447) := by
  have h := suzukiDF6D4FixedGridShard146Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard146EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 447)) at h
  exact h

def suzukiDF6D4FixedGridShard146EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard146EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard146EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard146EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard146EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard146EvenResidualData =
      suzukiDF6D4FixedGridShard146EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard146Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard146EvenResidualData =
    suzukiDF6D4FixedGridShard146EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard146EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard146EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 447 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 447) := by
    rw [suzukiDF6D4FixedGridShard146EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 447
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146EvenDotSoundness i
          suzukiDF6D4FixedGridShard146EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 447) := by
    simpa [suzukiDF6D4FixedGridShard146EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard146EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 447) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 447) := by
    rw [suzukiDF6D4FixedGridShard146EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 447
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard146EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard146EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard146EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard146EvenDotSoundness i
            suzukiDF6D4FixedGridShard146EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard146EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard146OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard146OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 447) := by
  have h := suzukiDF6D4FixedGridShard146Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard146OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 447)) at h
  exact h

theorem suzukiDF6D4FixedGridShard146OddFull_eq_live :
    suzukiDF6D4FixedGridShard146OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 447) := by
  have h := suzukiDF6D4FixedGridShard146Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard146OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 447)) at h
  exact h

def suzukiDF6D4FixedGridShard146OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard146OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard146OddDotSoundness i.val
        suzukiDF6D4FixedGridShard146OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard146OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard146OddResidualData =
      suzukiDF6D4FixedGridShard146OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard146Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard146OddResidualData =
    suzukiDF6D4FixedGridShard146OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard146OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard146OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 447 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 447) := by
    rw [suzukiDF6D4FixedGridShard146OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 447
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146OddDotSoundness i
          suzukiDF6D4FixedGridShard146OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 447) := by
    simpa [suzukiDF6D4FixedGridShard146OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard146OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 447) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard146OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 447) := by
    rw [suzukiDF6D4FixedGridShard146OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 447
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard146OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard146OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard146OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard146OddDotSoundness i
            suzukiDF6D4FixedGridShard146OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard146OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
