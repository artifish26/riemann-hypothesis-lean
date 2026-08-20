import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard098Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard098Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard098EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard098EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 98 k) := by
  have h := suzukiDF6D4FixedGridShard098Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard098EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 98 k)) at h
  exact h

def suzukiDF6D4FixedGridShard098EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard098EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard098EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard098EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard098EvenComparisonData)

theorem suzukiDF6D4FixedGridShard098EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard098EvenSolveData =
      suzukiDF6D4FixedGridShard098EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard098Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard098EvenSolveData =
    suzukiDF6D4FixedGridShard098EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard098EvenCross_eq_live :
    suzukiDF6D4FixedGridShard098EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 98) := by
  have h := suzukiDF6D4FixedGridShard098Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard098EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 98)) at h
  exact h

theorem suzukiDF6D4FixedGridShard098EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard098EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 98 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 98 k) := by
    rw [suzukiDF6D4FixedGridShard098EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 98 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098EvenDotSoundness i
          suzukiDF6D4FixedGridShard098EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 98 k) := by
    simpa [suzukiDF6D4FixedGridShard098EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard098EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 98 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 98) := by
    rw [suzukiDF6D4FixedGridShard098EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 98)
  rw [suzukiDF6D4FixedGridShard098EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard098EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard098EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard098EvenDotSoundness i
            suzukiDF6D4FixedGridShard098EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard098EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard098OddComparison_eq_live :
    suzukiDF6D4FixedGridShard098OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 98 k) := by
  have h := suzukiDF6D4FixedGridShard098Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard098OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 98 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard098OddCross_eq_live :
    suzukiDF6D4FixedGridShard098OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 98) := by
  have h := suzukiDF6D4FixedGridShard098Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard098OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 98)) at h
  exact h

def suzukiDF6D4FixedGridShard098OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard098OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard098OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard098OddDotSoundness i.val
      suzukiDF6D4FixedGridShard098OddComparisonData)

theorem suzukiDF6D4FixedGridShard098OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard098OddSolveData =
      suzukiDF6D4FixedGridShard098OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard098Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard098OddSolveData =
    suzukiDF6D4FixedGridShard098OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard098OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard098OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 98 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 98 k) := by
    rw [suzukiDF6D4FixedGridShard098OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 98 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098OddDotSoundness i
          suzukiDF6D4FixedGridShard098OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 98 k) := by
    simpa [suzukiDF6D4FixedGridShard098OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard098OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 98 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 98) := by
    rw [suzukiDF6D4FixedGridShard098OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 98)
  rw [suzukiDF6D4FixedGridShard098OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard098OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard098OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard098OddDotSoundness i
            suzukiDF6D4FixedGridShard098OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard098OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard098EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard098EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 399) := by
  have h := suzukiDF6D4FixedGridShard098Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard098EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 399)) at h
  exact h

theorem suzukiDF6D4FixedGridShard098EvenFull_eq_live :
    suzukiDF6D4FixedGridShard098EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 399) := by
  have h := suzukiDF6D4FixedGridShard098Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard098EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 399)) at h
  exact h

def suzukiDF6D4FixedGridShard098EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard098EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard098EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard098EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard098EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard098EvenResidualData =
      suzukiDF6D4FixedGridShard098EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard098Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard098EvenResidualData =
    suzukiDF6D4FixedGridShard098EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard098EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard098EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 399 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 399) := by
    rw [suzukiDF6D4FixedGridShard098EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 399
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098EvenDotSoundness i
          suzukiDF6D4FixedGridShard098EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 399) := by
    simpa [suzukiDF6D4FixedGridShard098EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard098EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 399) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 399) := by
    rw [suzukiDF6D4FixedGridShard098EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 399
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard098EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard098EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard098EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard098EvenDotSoundness i
            suzukiDF6D4FixedGridShard098EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard098EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard098OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard098OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 399) := by
  have h := suzukiDF6D4FixedGridShard098Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard098OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 399)) at h
  exact h

theorem suzukiDF6D4FixedGridShard098OddFull_eq_live :
    suzukiDF6D4FixedGridShard098OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 399) := by
  have h := suzukiDF6D4FixedGridShard098Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard098OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 399)) at h
  exact h

def suzukiDF6D4FixedGridShard098OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard098OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard098OddDotSoundness i.val
        suzukiDF6D4FixedGridShard098OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard098OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard098OddResidualData =
      suzukiDF6D4FixedGridShard098OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard098Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard098OddResidualData =
    suzukiDF6D4FixedGridShard098OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard098OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard098OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 399 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 399) := by
    rw [suzukiDF6D4FixedGridShard098OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 399
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098OddDotSoundness i
          suzukiDF6D4FixedGridShard098OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 399) := by
    simpa [suzukiDF6D4FixedGridShard098OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard098OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 399) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard098OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 399) := by
    rw [suzukiDF6D4FixedGridShard098OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 399
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard098OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard098OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard098OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard098OddDotSoundness i
            suzukiDF6D4FixedGridShard098OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard098OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
