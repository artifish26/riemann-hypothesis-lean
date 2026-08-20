import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard216Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard216Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard216EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard216EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 216 k) := by
  have h := suzukiDF6D4FixedGridShard216Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard216EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 216 k)) at h
  exact h

def suzukiDF6D4FixedGridShard216EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard216EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard216EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard216EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard216EvenComparisonData)

theorem suzukiDF6D4FixedGridShard216EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard216EvenSolveData =
      suzukiDF6D4FixedGridShard216EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard216Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard216EvenSolveData =
    suzukiDF6D4FixedGridShard216EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard216EvenCross_eq_live :
    suzukiDF6D4FixedGridShard216EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 216) := by
  have h := suzukiDF6D4FixedGridShard216Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard216EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 216)) at h
  exact h

theorem suzukiDF6D4FixedGridShard216EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard216EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 216 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 216 k) := by
    rw [suzukiDF6D4FixedGridShard216EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 216 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216EvenDotSoundness i
          suzukiDF6D4FixedGridShard216EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 216 k) := by
    simpa [suzukiDF6D4FixedGridShard216EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard216EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 216 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 216) := by
    rw [suzukiDF6D4FixedGridShard216EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 216)
  rw [suzukiDF6D4FixedGridShard216EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard216EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard216EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard216EvenDotSoundness i
            suzukiDF6D4FixedGridShard216EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard216EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard216OddComparison_eq_live :
    suzukiDF6D4FixedGridShard216OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 216 k) := by
  have h := suzukiDF6D4FixedGridShard216Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard216OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 216 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard216OddCross_eq_live :
    suzukiDF6D4FixedGridShard216OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 216) := by
  have h := suzukiDF6D4FixedGridShard216Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard216OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 216)) at h
  exact h

def suzukiDF6D4FixedGridShard216OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard216OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard216OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard216OddDotSoundness i.val
      suzukiDF6D4FixedGridShard216OddComparisonData)

theorem suzukiDF6D4FixedGridShard216OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard216OddSolveData =
      suzukiDF6D4FixedGridShard216OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard216Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard216OddSolveData =
    suzukiDF6D4FixedGridShard216OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard216OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard216OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 216 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 216 k) := by
    rw [suzukiDF6D4FixedGridShard216OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 216 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216OddDotSoundness i
          suzukiDF6D4FixedGridShard216OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 216 k) := by
    simpa [suzukiDF6D4FixedGridShard216OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard216OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 216 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 216) := by
    rw [suzukiDF6D4FixedGridShard216OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 216)
  rw [suzukiDF6D4FixedGridShard216OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard216OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard216OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard216OddDotSoundness i
            suzukiDF6D4FixedGridShard216OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard216OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard216EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard216EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 517) := by
  have h := suzukiDF6D4FixedGridShard216Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard216EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 517)) at h
  exact h

theorem suzukiDF6D4FixedGridShard216EvenFull_eq_live :
    suzukiDF6D4FixedGridShard216EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 517) := by
  have h := suzukiDF6D4FixedGridShard216Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard216EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 517)) at h
  exact h

def suzukiDF6D4FixedGridShard216EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard216EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard216EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard216EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard216EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard216EvenResidualData =
      suzukiDF6D4FixedGridShard216EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard216Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard216EvenResidualData =
    suzukiDF6D4FixedGridShard216EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard216EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard216EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 517 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 517) := by
    rw [suzukiDF6D4FixedGridShard216EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 517
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216EvenDotSoundness i
          suzukiDF6D4FixedGridShard216EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 517) := by
    simpa [suzukiDF6D4FixedGridShard216EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard216EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 517) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 517) := by
    rw [suzukiDF6D4FixedGridShard216EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 517
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard216EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard216EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard216EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard216EvenDotSoundness i
            suzukiDF6D4FixedGridShard216EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard216EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard216OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard216OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 517) := by
  have h := suzukiDF6D4FixedGridShard216Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard216OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 517)) at h
  exact h

theorem suzukiDF6D4FixedGridShard216OddFull_eq_live :
    suzukiDF6D4FixedGridShard216OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 517) := by
  have h := suzukiDF6D4FixedGridShard216Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard216OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 517)) at h
  exact h

def suzukiDF6D4FixedGridShard216OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard216OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard216OddDotSoundness i.val
        suzukiDF6D4FixedGridShard216OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard216OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard216OddResidualData =
      suzukiDF6D4FixedGridShard216OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard216Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard216OddResidualData =
    suzukiDF6D4FixedGridShard216OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard216OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard216OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 517 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 517) := by
    rw [suzukiDF6D4FixedGridShard216OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 517
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216OddDotSoundness i
          suzukiDF6D4FixedGridShard216OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 517) := by
    simpa [suzukiDF6D4FixedGridShard216OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard216OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 517) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard216OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 517) := by
    rw [suzukiDF6D4FixedGridShard216OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 517
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard216OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard216OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard216OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard216OddDotSoundness i
            suzukiDF6D4FixedGridShard216OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard216OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
