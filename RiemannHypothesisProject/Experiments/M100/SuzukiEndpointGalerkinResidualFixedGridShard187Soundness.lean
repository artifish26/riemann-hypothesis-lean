import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard187Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard187Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard187EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard187EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 187 k) := by
  have h := suzukiDF6D4FixedGridShard187Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard187EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 187 k)) at h
  exact h

def suzukiDF6D4FixedGridShard187EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard187EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard187EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard187EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard187EvenComparisonData)

theorem suzukiDF6D4FixedGridShard187EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard187EvenSolveData =
      suzukiDF6D4FixedGridShard187EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard187Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard187EvenSolveData =
    suzukiDF6D4FixedGridShard187EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard187EvenCross_eq_live :
    suzukiDF6D4FixedGridShard187EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 187) := by
  have h := suzukiDF6D4FixedGridShard187Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard187EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 187)) at h
  exact h

theorem suzukiDF6D4FixedGridShard187EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard187EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 187 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 187 k) := by
    rw [suzukiDF6D4FixedGridShard187EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 187 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187EvenDotSoundness i
          suzukiDF6D4FixedGridShard187EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 187 k) := by
    simpa [suzukiDF6D4FixedGridShard187EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard187EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 187 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 187) := by
    rw [suzukiDF6D4FixedGridShard187EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 187)
  rw [suzukiDF6D4FixedGridShard187EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard187EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard187EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard187EvenDotSoundness i
            suzukiDF6D4FixedGridShard187EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard187EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard187OddComparison_eq_live :
    suzukiDF6D4FixedGridShard187OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 187 k) := by
  have h := suzukiDF6D4FixedGridShard187Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard187OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 187 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard187OddCross_eq_live :
    suzukiDF6D4FixedGridShard187OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 187) := by
  have h := suzukiDF6D4FixedGridShard187Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard187OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 187)) at h
  exact h

def suzukiDF6D4FixedGridShard187OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard187OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard187OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard187OddDotSoundness i.val
      suzukiDF6D4FixedGridShard187OddComparisonData)

theorem suzukiDF6D4FixedGridShard187OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard187OddSolveData =
      suzukiDF6D4FixedGridShard187OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard187Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard187OddSolveData =
    suzukiDF6D4FixedGridShard187OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard187OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard187OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 187 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 187 k) := by
    rw [suzukiDF6D4FixedGridShard187OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 187 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187OddDotSoundness i
          suzukiDF6D4FixedGridShard187OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 187 k) := by
    simpa [suzukiDF6D4FixedGridShard187OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard187OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 187 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 187) := by
    rw [suzukiDF6D4FixedGridShard187OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 187)
  rw [suzukiDF6D4FixedGridShard187OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard187OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard187OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard187OddDotSoundness i
            suzukiDF6D4FixedGridShard187OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard187OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard187EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard187EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 488) := by
  have h := suzukiDF6D4FixedGridShard187Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard187EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 488)) at h
  exact h

theorem suzukiDF6D4FixedGridShard187EvenFull_eq_live :
    suzukiDF6D4FixedGridShard187EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 488) := by
  have h := suzukiDF6D4FixedGridShard187Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard187EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 488)) at h
  exact h

def suzukiDF6D4FixedGridShard187EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard187EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard187EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard187EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard187EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard187EvenResidualData =
      suzukiDF6D4FixedGridShard187EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard187Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard187EvenResidualData =
    suzukiDF6D4FixedGridShard187EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard187EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard187EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 488 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 488) := by
    rw [suzukiDF6D4FixedGridShard187EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 488
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187EvenDotSoundness i
          suzukiDF6D4FixedGridShard187EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 488) := by
    simpa [suzukiDF6D4FixedGridShard187EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard187EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 488) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 488) := by
    rw [suzukiDF6D4FixedGridShard187EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 488
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard187EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard187EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard187EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard187EvenDotSoundness i
            suzukiDF6D4FixedGridShard187EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard187EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard187OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard187OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 488) := by
  have h := suzukiDF6D4FixedGridShard187Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard187OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 488)) at h
  exact h

theorem suzukiDF6D4FixedGridShard187OddFull_eq_live :
    suzukiDF6D4FixedGridShard187OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 488) := by
  have h := suzukiDF6D4FixedGridShard187Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard187OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 488)) at h
  exact h

def suzukiDF6D4FixedGridShard187OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard187OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard187OddDotSoundness i.val
        suzukiDF6D4FixedGridShard187OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard187OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard187OddResidualData =
      suzukiDF6D4FixedGridShard187OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard187Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard187OddResidualData =
    suzukiDF6D4FixedGridShard187OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard187OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard187OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 488 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 488) := by
    rw [suzukiDF6D4FixedGridShard187OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 488
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187OddDotSoundness i
          suzukiDF6D4FixedGridShard187OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 488) := by
    simpa [suzukiDF6D4FixedGridShard187OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard187OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 488) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard187OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 488) := by
    rw [suzukiDF6D4FixedGridShard187OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 488
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard187OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard187OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard187OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard187OddDotSoundness i
            suzukiDF6D4FixedGridShard187OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard187OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
