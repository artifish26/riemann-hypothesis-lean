import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard055Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard055Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard055EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard055EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 55 k) := by
  have h := suzukiDF6D4FixedGridShard055Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard055EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 55 k)) at h
  exact h

def suzukiDF6D4FixedGridShard055EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard055EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard055EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard055EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard055EvenComparisonData)

theorem suzukiDF6D4FixedGridShard055EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard055EvenSolveData =
      suzukiDF6D4FixedGridShard055EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard055Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard055EvenSolveData =
    suzukiDF6D4FixedGridShard055EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard055EvenCross_eq_live :
    suzukiDF6D4FixedGridShard055EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 55) := by
  have h := suzukiDF6D4FixedGridShard055Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard055EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 55)) at h
  exact h

theorem suzukiDF6D4FixedGridShard055EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard055EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 55 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 55 k) := by
    rw [suzukiDF6D4FixedGridShard055EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 55 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055EvenDotSoundness i
          suzukiDF6D4FixedGridShard055EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 55 k) := by
    simpa [suzukiDF6D4FixedGridShard055EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard055EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 55 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 55) := by
    rw [suzukiDF6D4FixedGridShard055EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 55)
  rw [suzukiDF6D4FixedGridShard055EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard055EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard055EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard055EvenDotSoundness i
            suzukiDF6D4FixedGridShard055EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard055EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard055OddComparison_eq_live :
    suzukiDF6D4FixedGridShard055OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 55 k) := by
  have h := suzukiDF6D4FixedGridShard055Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard055OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 55 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard055OddCross_eq_live :
    suzukiDF6D4FixedGridShard055OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 55) := by
  have h := suzukiDF6D4FixedGridShard055Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard055OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 55)) at h
  exact h

def suzukiDF6D4FixedGridShard055OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard055OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard055OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard055OddDotSoundness i.val
      suzukiDF6D4FixedGridShard055OddComparisonData)

theorem suzukiDF6D4FixedGridShard055OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard055OddSolveData =
      suzukiDF6D4FixedGridShard055OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard055Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard055OddSolveData =
    suzukiDF6D4FixedGridShard055OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard055OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard055OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 55 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 55 k) := by
    rw [suzukiDF6D4FixedGridShard055OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 55 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055OddDotSoundness i
          suzukiDF6D4FixedGridShard055OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 55 k) := by
    simpa [suzukiDF6D4FixedGridShard055OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard055OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 55 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 55) := by
    rw [suzukiDF6D4FixedGridShard055OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 55)
  rw [suzukiDF6D4FixedGridShard055OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard055OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard055OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard055OddDotSoundness i
            suzukiDF6D4FixedGridShard055OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard055OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard055EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard055EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 356) := by
  have h := suzukiDF6D4FixedGridShard055Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard055EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 356)) at h
  exact h

theorem suzukiDF6D4FixedGridShard055EvenFull_eq_live :
    suzukiDF6D4FixedGridShard055EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 356) := by
  have h := suzukiDF6D4FixedGridShard055Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard055EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 356)) at h
  exact h

def suzukiDF6D4FixedGridShard055EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard055EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard055EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard055EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard055EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard055EvenResidualData =
      suzukiDF6D4FixedGridShard055EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard055Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard055EvenResidualData =
    suzukiDF6D4FixedGridShard055EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard055EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard055EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 356 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 356) := by
    rw [suzukiDF6D4FixedGridShard055EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 356
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055EvenDotSoundness i
          suzukiDF6D4FixedGridShard055EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 356) := by
    simpa [suzukiDF6D4FixedGridShard055EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard055EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 356) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 356) := by
    rw [suzukiDF6D4FixedGridShard055EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 356
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard055EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard055EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard055EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard055EvenDotSoundness i
            suzukiDF6D4FixedGridShard055EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard055EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard055OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard055OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 356) := by
  have h := suzukiDF6D4FixedGridShard055Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard055OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 356)) at h
  exact h

theorem suzukiDF6D4FixedGridShard055OddFull_eq_live :
    suzukiDF6D4FixedGridShard055OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 356) := by
  have h := suzukiDF6D4FixedGridShard055Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard055OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 356)) at h
  exact h

def suzukiDF6D4FixedGridShard055OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard055OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard055OddDotSoundness i.val
        suzukiDF6D4FixedGridShard055OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard055OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard055OddResidualData =
      suzukiDF6D4FixedGridShard055OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard055Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard055OddResidualData =
    suzukiDF6D4FixedGridShard055OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard055OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard055OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 356 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 356) := by
    rw [suzukiDF6D4FixedGridShard055OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 356
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055OddDotSoundness i
          suzukiDF6D4FixedGridShard055OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 356) := by
    simpa [suzukiDF6D4FixedGridShard055OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard055OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 356) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard055OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 356) := by
    rw [suzukiDF6D4FixedGridShard055OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 356
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard055OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard055OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard055OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard055OddDotSoundness i
            suzukiDF6D4FixedGridShard055OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard055OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
