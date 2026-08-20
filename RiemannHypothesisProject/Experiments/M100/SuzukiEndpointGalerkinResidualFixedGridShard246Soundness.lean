import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard246Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard246Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard246EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard246EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 246 k) := by
  have h := suzukiDF6D4FixedGridShard246Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard246EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 246 k)) at h
  exact h

def suzukiDF6D4FixedGridShard246EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard246EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard246EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard246EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard246EvenComparisonData)

theorem suzukiDF6D4FixedGridShard246EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard246EvenSolveData =
      suzukiDF6D4FixedGridShard246EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard246Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard246EvenSolveData =
    suzukiDF6D4FixedGridShard246EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard246EvenCross_eq_live :
    suzukiDF6D4FixedGridShard246EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 246) := by
  have h := suzukiDF6D4FixedGridShard246Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard246EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 246)) at h
  exact h

theorem suzukiDF6D4FixedGridShard246EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard246EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 246 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 246 k) := by
    rw [suzukiDF6D4FixedGridShard246EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 246 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246EvenDotSoundness i
          suzukiDF6D4FixedGridShard246EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 246 k) := by
    simpa [suzukiDF6D4FixedGridShard246EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard246EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 246 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 246) := by
    rw [suzukiDF6D4FixedGridShard246EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 246)
  rw [suzukiDF6D4FixedGridShard246EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard246EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard246EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard246EvenDotSoundness i
            suzukiDF6D4FixedGridShard246EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard246EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard246OddComparison_eq_live :
    suzukiDF6D4FixedGridShard246OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 246 k) := by
  have h := suzukiDF6D4FixedGridShard246Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard246OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 246 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard246OddCross_eq_live :
    suzukiDF6D4FixedGridShard246OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 246) := by
  have h := suzukiDF6D4FixedGridShard246Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard246OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 246)) at h
  exact h

def suzukiDF6D4FixedGridShard246OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard246OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard246OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard246OddDotSoundness i.val
      suzukiDF6D4FixedGridShard246OddComparisonData)

theorem suzukiDF6D4FixedGridShard246OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard246OddSolveData =
      suzukiDF6D4FixedGridShard246OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard246Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard246OddSolveData =
    suzukiDF6D4FixedGridShard246OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard246OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard246OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 246 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 246 k) := by
    rw [suzukiDF6D4FixedGridShard246OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 246 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246OddDotSoundness i
          suzukiDF6D4FixedGridShard246OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 246 k) := by
    simpa [suzukiDF6D4FixedGridShard246OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard246OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 246 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 246) := by
    rw [suzukiDF6D4FixedGridShard246OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 246)
  rw [suzukiDF6D4FixedGridShard246OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard246OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard246OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard246OddDotSoundness i
            suzukiDF6D4FixedGridShard246OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard246OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard246EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard246EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 547) := by
  have h := suzukiDF6D4FixedGridShard246Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard246EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 547)) at h
  exact h

theorem suzukiDF6D4FixedGridShard246EvenFull_eq_live :
    suzukiDF6D4FixedGridShard246EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 547) := by
  have h := suzukiDF6D4FixedGridShard246Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard246EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 547)) at h
  exact h

def suzukiDF6D4FixedGridShard246EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard246EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard246EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard246EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard246EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard246EvenResidualData =
      suzukiDF6D4FixedGridShard246EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard246Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard246EvenResidualData =
    suzukiDF6D4FixedGridShard246EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard246EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard246EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 547 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 547) := by
    rw [suzukiDF6D4FixedGridShard246EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 547
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246EvenDotSoundness i
          suzukiDF6D4FixedGridShard246EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 547) := by
    simpa [suzukiDF6D4FixedGridShard246EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard246EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 547) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 547) := by
    rw [suzukiDF6D4FixedGridShard246EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 547
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard246EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard246EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard246EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard246EvenDotSoundness i
            suzukiDF6D4FixedGridShard246EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard246EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard246OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard246OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 547) := by
  have h := suzukiDF6D4FixedGridShard246Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard246OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 547)) at h
  exact h

theorem suzukiDF6D4FixedGridShard246OddFull_eq_live :
    suzukiDF6D4FixedGridShard246OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 547) := by
  have h := suzukiDF6D4FixedGridShard246Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard246OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 547)) at h
  exact h

def suzukiDF6D4FixedGridShard246OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard246OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard246OddDotSoundness i.val
        suzukiDF6D4FixedGridShard246OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard246OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard246OddResidualData =
      suzukiDF6D4FixedGridShard246OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard246Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard246OddResidualData =
    suzukiDF6D4FixedGridShard246OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard246OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard246OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 547 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 547) := by
    rw [suzukiDF6D4FixedGridShard246OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 547
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246OddDotSoundness i
          suzukiDF6D4FixedGridShard246OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 547) := by
    simpa [suzukiDF6D4FixedGridShard246OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard246OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 547) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard246OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 547) := by
    rw [suzukiDF6D4FixedGridShard246OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 547
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard246OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard246OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard246OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard246OddDotSoundness i
            suzukiDF6D4FixedGridShard246OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard246OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
