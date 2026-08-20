import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard022Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard022Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard022EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard022EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 22 k) := by
  have h := suzukiDF6D4FixedGridShard022Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard022EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 22 k)) at h
  exact h

def suzukiDF6D4FixedGridShard022EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard022EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard022EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard022EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard022EvenComparisonData)

theorem suzukiDF6D4FixedGridShard022EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard022EvenSolveData =
      suzukiDF6D4FixedGridShard022EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard022Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard022EvenSolveData =
    suzukiDF6D4FixedGridShard022EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard022EvenCross_eq_live :
    suzukiDF6D4FixedGridShard022EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 22) := by
  have h := suzukiDF6D4FixedGridShard022Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard022EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 22)) at h
  exact h

theorem suzukiDF6D4FixedGridShard022EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard022EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 22 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 22 k) := by
    rw [suzukiDF6D4FixedGridShard022EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 22 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022EvenDotSoundness i
          suzukiDF6D4FixedGridShard022EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 22 k) := by
    simpa [suzukiDF6D4FixedGridShard022EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard022EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 22 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 22) := by
    rw [suzukiDF6D4FixedGridShard022EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 22)
  rw [suzukiDF6D4FixedGridShard022EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard022EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard022EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard022EvenDotSoundness i
            suzukiDF6D4FixedGridShard022EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard022EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard022OddComparison_eq_live :
    suzukiDF6D4FixedGridShard022OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 22 k) := by
  have h := suzukiDF6D4FixedGridShard022Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard022OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 22 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard022OddCross_eq_live :
    suzukiDF6D4FixedGridShard022OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 22) := by
  have h := suzukiDF6D4FixedGridShard022Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard022OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 22)) at h
  exact h

def suzukiDF6D4FixedGridShard022OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard022OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard022OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard022OddDotSoundness i.val
      suzukiDF6D4FixedGridShard022OddComparisonData)

theorem suzukiDF6D4FixedGridShard022OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard022OddSolveData =
      suzukiDF6D4FixedGridShard022OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard022Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard022OddSolveData =
    suzukiDF6D4FixedGridShard022OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard022OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard022OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 22 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 22 k) := by
    rw [suzukiDF6D4FixedGridShard022OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 22 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022OddDotSoundness i
          suzukiDF6D4FixedGridShard022OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 22 k) := by
    simpa [suzukiDF6D4FixedGridShard022OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard022OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 22 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 22) := by
    rw [suzukiDF6D4FixedGridShard022OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 22)
  rw [suzukiDF6D4FixedGridShard022OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard022OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard022OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard022OddDotSoundness i
            suzukiDF6D4FixedGridShard022OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard022OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard022EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard022EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 323) := by
  have h := suzukiDF6D4FixedGridShard022Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard022EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 323)) at h
  exact h

theorem suzukiDF6D4FixedGridShard022EvenFull_eq_live :
    suzukiDF6D4FixedGridShard022EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 323) := by
  have h := suzukiDF6D4FixedGridShard022Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard022EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 323)) at h
  exact h

def suzukiDF6D4FixedGridShard022EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard022EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard022EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard022EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard022EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard022EvenResidualData =
      suzukiDF6D4FixedGridShard022EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard022Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard022EvenResidualData =
    suzukiDF6D4FixedGridShard022EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard022EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard022EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 323 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 323) := by
    rw [suzukiDF6D4FixedGridShard022EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 323
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022EvenDotSoundness i
          suzukiDF6D4FixedGridShard022EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 323) := by
    simpa [suzukiDF6D4FixedGridShard022EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard022EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 323) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 323) := by
    rw [suzukiDF6D4FixedGridShard022EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 323
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard022EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard022EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard022EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard022EvenDotSoundness i
            suzukiDF6D4FixedGridShard022EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard022EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard022OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard022OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 323) := by
  have h := suzukiDF6D4FixedGridShard022Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard022OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 323)) at h
  exact h

theorem suzukiDF6D4FixedGridShard022OddFull_eq_live :
    suzukiDF6D4FixedGridShard022OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 323) := by
  have h := suzukiDF6D4FixedGridShard022Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard022OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 323)) at h
  exact h

def suzukiDF6D4FixedGridShard022OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard022OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard022OddDotSoundness i.val
        suzukiDF6D4FixedGridShard022OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard022OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard022OddResidualData =
      suzukiDF6D4FixedGridShard022OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard022Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard022OddResidualData =
    suzukiDF6D4FixedGridShard022OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard022OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard022OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 323 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 323) := by
    rw [suzukiDF6D4FixedGridShard022OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 323
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022OddDotSoundness i
          suzukiDF6D4FixedGridShard022OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 323) := by
    simpa [suzukiDF6D4FixedGridShard022OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard022OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 323) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard022OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 323) := by
    rw [suzukiDF6D4FixedGridShard022OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 323
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard022OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard022OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard022OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard022OddDotSoundness i
            suzukiDF6D4FixedGridShard022OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard022OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
