import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard117Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard117Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard117EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard117EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 117 k) := by
  have h := suzukiDF6D4FixedGridShard117Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard117EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 117 k)) at h
  exact h

def suzukiDF6D4FixedGridShard117EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard117EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard117EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard117EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard117EvenComparisonData)

theorem suzukiDF6D4FixedGridShard117EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard117EvenSolveData =
      suzukiDF6D4FixedGridShard117EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard117Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard117EvenSolveData =
    suzukiDF6D4FixedGridShard117EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard117EvenCross_eq_live :
    suzukiDF6D4FixedGridShard117EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 117) := by
  have h := suzukiDF6D4FixedGridShard117Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard117EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 117)) at h
  exact h

theorem suzukiDF6D4FixedGridShard117EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard117EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 117 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 117 k) := by
    rw [suzukiDF6D4FixedGridShard117EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 117 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117EvenDotSoundness i
          suzukiDF6D4FixedGridShard117EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 117 k) := by
    simpa [suzukiDF6D4FixedGridShard117EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard117EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 117 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 117) := by
    rw [suzukiDF6D4FixedGridShard117EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 117)
  rw [suzukiDF6D4FixedGridShard117EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard117EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard117EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard117EvenDotSoundness i
            suzukiDF6D4FixedGridShard117EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard117EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard117OddComparison_eq_live :
    suzukiDF6D4FixedGridShard117OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 117 k) := by
  have h := suzukiDF6D4FixedGridShard117Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard117OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 117 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard117OddCross_eq_live :
    suzukiDF6D4FixedGridShard117OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 117) := by
  have h := suzukiDF6D4FixedGridShard117Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard117OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 117)) at h
  exact h

def suzukiDF6D4FixedGridShard117OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard117OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard117OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard117OddDotSoundness i.val
      suzukiDF6D4FixedGridShard117OddComparisonData)

theorem suzukiDF6D4FixedGridShard117OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard117OddSolveData =
      suzukiDF6D4FixedGridShard117OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard117Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard117OddSolveData =
    suzukiDF6D4FixedGridShard117OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard117OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard117OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 117 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 117 k) := by
    rw [suzukiDF6D4FixedGridShard117OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 117 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117OddDotSoundness i
          suzukiDF6D4FixedGridShard117OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 117 k) := by
    simpa [suzukiDF6D4FixedGridShard117OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard117OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 117 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 117) := by
    rw [suzukiDF6D4FixedGridShard117OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 117)
  rw [suzukiDF6D4FixedGridShard117OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard117OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard117OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard117OddDotSoundness i
            suzukiDF6D4FixedGridShard117OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard117OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard117EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard117EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 418) := by
  have h := suzukiDF6D4FixedGridShard117Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard117EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 418)) at h
  exact h

theorem suzukiDF6D4FixedGridShard117EvenFull_eq_live :
    suzukiDF6D4FixedGridShard117EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 418) := by
  have h := suzukiDF6D4FixedGridShard117Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard117EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 418)) at h
  exact h

def suzukiDF6D4FixedGridShard117EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard117EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard117EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard117EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard117EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard117EvenResidualData =
      suzukiDF6D4FixedGridShard117EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard117Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard117EvenResidualData =
    suzukiDF6D4FixedGridShard117EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard117EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard117EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 418 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 418) := by
    rw [suzukiDF6D4FixedGridShard117EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 418
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117EvenDotSoundness i
          suzukiDF6D4FixedGridShard117EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 418) := by
    simpa [suzukiDF6D4FixedGridShard117EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard117EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 418) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 418) := by
    rw [suzukiDF6D4FixedGridShard117EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 418
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard117EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard117EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard117EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard117EvenDotSoundness i
            suzukiDF6D4FixedGridShard117EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard117EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard117OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard117OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 418) := by
  have h := suzukiDF6D4FixedGridShard117Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard117OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 418)) at h
  exact h

theorem suzukiDF6D4FixedGridShard117OddFull_eq_live :
    suzukiDF6D4FixedGridShard117OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 418) := by
  have h := suzukiDF6D4FixedGridShard117Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard117OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 418)) at h
  exact h

def suzukiDF6D4FixedGridShard117OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard117OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard117OddDotSoundness i.val
        suzukiDF6D4FixedGridShard117OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard117OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard117OddResidualData =
      suzukiDF6D4FixedGridShard117OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard117Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard117OddResidualData =
    suzukiDF6D4FixedGridShard117OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard117OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard117OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 418 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 418) := by
    rw [suzukiDF6D4FixedGridShard117OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 418
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117OddDotSoundness i
          suzukiDF6D4FixedGridShard117OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 418) := by
    simpa [suzukiDF6D4FixedGridShard117OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard117OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 418) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard117OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 418) := by
    rw [suzukiDF6D4FixedGridShard117OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 418
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard117OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard117OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard117OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard117OddDotSoundness i
            suzukiDF6D4FixedGridShard117OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard117OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
