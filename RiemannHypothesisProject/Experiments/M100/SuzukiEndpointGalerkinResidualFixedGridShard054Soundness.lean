import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard054Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard054Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard054EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard054EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 54 k) := by
  have h := suzukiDF6D4FixedGridShard054Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard054EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 54 k)) at h
  exact h

def suzukiDF6D4FixedGridShard054EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard054EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard054EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard054EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard054EvenComparisonData)

theorem suzukiDF6D4FixedGridShard054EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard054EvenSolveData =
      suzukiDF6D4FixedGridShard054EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard054Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard054EvenSolveData =
    suzukiDF6D4FixedGridShard054EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard054EvenCross_eq_live :
    suzukiDF6D4FixedGridShard054EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 54) := by
  have h := suzukiDF6D4FixedGridShard054Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard054EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 54)) at h
  exact h

theorem suzukiDF6D4FixedGridShard054EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard054EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 54 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 54 k) := by
    rw [suzukiDF6D4FixedGridShard054EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 54 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054EvenDotSoundness i
          suzukiDF6D4FixedGridShard054EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 54 k) := by
    simpa [suzukiDF6D4FixedGridShard054EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard054EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 54 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 54) := by
    rw [suzukiDF6D4FixedGridShard054EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 54)
  rw [suzukiDF6D4FixedGridShard054EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard054EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard054EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard054EvenDotSoundness i
            suzukiDF6D4FixedGridShard054EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard054EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard054OddComparison_eq_live :
    suzukiDF6D4FixedGridShard054OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 54 k) := by
  have h := suzukiDF6D4FixedGridShard054Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard054OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 54 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard054OddCross_eq_live :
    suzukiDF6D4FixedGridShard054OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 54) := by
  have h := suzukiDF6D4FixedGridShard054Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard054OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 54)) at h
  exact h

def suzukiDF6D4FixedGridShard054OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard054OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard054OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard054OddDotSoundness i.val
      suzukiDF6D4FixedGridShard054OddComparisonData)

theorem suzukiDF6D4FixedGridShard054OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard054OddSolveData =
      suzukiDF6D4FixedGridShard054OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard054Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard054OddSolveData =
    suzukiDF6D4FixedGridShard054OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard054OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard054OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 54 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 54 k) := by
    rw [suzukiDF6D4FixedGridShard054OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 54 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054OddDotSoundness i
          suzukiDF6D4FixedGridShard054OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 54 k) := by
    simpa [suzukiDF6D4FixedGridShard054OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard054OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 54 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 54) := by
    rw [suzukiDF6D4FixedGridShard054OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 54)
  rw [suzukiDF6D4FixedGridShard054OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard054OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard054OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard054OddDotSoundness i
            suzukiDF6D4FixedGridShard054OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard054OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard054EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard054EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 355) := by
  have h := suzukiDF6D4FixedGridShard054Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard054EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 355)) at h
  exact h

theorem suzukiDF6D4FixedGridShard054EvenFull_eq_live :
    suzukiDF6D4FixedGridShard054EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 355) := by
  have h := suzukiDF6D4FixedGridShard054Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard054EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 355)) at h
  exact h

def suzukiDF6D4FixedGridShard054EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard054EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard054EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard054EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard054EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard054EvenResidualData =
      suzukiDF6D4FixedGridShard054EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard054Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard054EvenResidualData =
    suzukiDF6D4FixedGridShard054EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard054EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard054EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 355 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 355) := by
    rw [suzukiDF6D4FixedGridShard054EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 355
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054EvenDotSoundness i
          suzukiDF6D4FixedGridShard054EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 355) := by
    simpa [suzukiDF6D4FixedGridShard054EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard054EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 355) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 355) := by
    rw [suzukiDF6D4FixedGridShard054EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 355
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard054EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard054EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard054EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard054EvenDotSoundness i
            suzukiDF6D4FixedGridShard054EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard054EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard054OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard054OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 355) := by
  have h := suzukiDF6D4FixedGridShard054Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard054OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 355)) at h
  exact h

theorem suzukiDF6D4FixedGridShard054OddFull_eq_live :
    suzukiDF6D4FixedGridShard054OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 355) := by
  have h := suzukiDF6D4FixedGridShard054Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard054OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 355)) at h
  exact h

def suzukiDF6D4FixedGridShard054OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard054OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard054OddDotSoundness i.val
        suzukiDF6D4FixedGridShard054OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard054OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard054OddResidualData =
      suzukiDF6D4FixedGridShard054OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard054Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard054OddResidualData =
    suzukiDF6D4FixedGridShard054OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard054OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard054OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 355 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 355) := by
    rw [suzukiDF6D4FixedGridShard054OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 355
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054OddDotSoundness i
          suzukiDF6D4FixedGridShard054OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 355) := by
    simpa [suzukiDF6D4FixedGridShard054OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard054OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 355) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard054OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 355) := by
    rw [suzukiDF6D4FixedGridShard054OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 355
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard054OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard054OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard054OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard054OddDotSoundness i
            suzukiDF6D4FixedGridShard054OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard054OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
