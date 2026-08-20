import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard135Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard135Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard135EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard135EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 135 k) := by
  have h := suzukiDF6D4FixedGridShard135Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard135EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 135 k)) at h
  exact h

def suzukiDF6D4FixedGridShard135EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard135EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard135EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard135EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard135EvenComparisonData)

theorem suzukiDF6D4FixedGridShard135EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard135EvenSolveData =
      suzukiDF6D4FixedGridShard135EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard135Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard135EvenSolveData =
    suzukiDF6D4FixedGridShard135EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard135EvenCross_eq_live :
    suzukiDF6D4FixedGridShard135EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 135) := by
  have h := suzukiDF6D4FixedGridShard135Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard135EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 135)) at h
  exact h

theorem suzukiDF6D4FixedGridShard135EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard135EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 135 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 135 k) := by
    rw [suzukiDF6D4FixedGridShard135EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 135 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135EvenDotSoundness i
          suzukiDF6D4FixedGridShard135EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 135 k) := by
    simpa [suzukiDF6D4FixedGridShard135EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard135EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 135 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 135) := by
    rw [suzukiDF6D4FixedGridShard135EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 135)
  rw [suzukiDF6D4FixedGridShard135EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard135EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard135EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard135EvenDotSoundness i
            suzukiDF6D4FixedGridShard135EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard135EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard135OddComparison_eq_live :
    suzukiDF6D4FixedGridShard135OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 135 k) := by
  have h := suzukiDF6D4FixedGridShard135Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard135OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 135 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard135OddCross_eq_live :
    suzukiDF6D4FixedGridShard135OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 135) := by
  have h := suzukiDF6D4FixedGridShard135Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard135OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 135)) at h
  exact h

def suzukiDF6D4FixedGridShard135OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard135OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard135OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard135OddDotSoundness i.val
      suzukiDF6D4FixedGridShard135OddComparisonData)

theorem suzukiDF6D4FixedGridShard135OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard135OddSolveData =
      suzukiDF6D4FixedGridShard135OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard135Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard135OddSolveData =
    suzukiDF6D4FixedGridShard135OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard135OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard135OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 135 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 135 k) := by
    rw [suzukiDF6D4FixedGridShard135OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 135 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135OddDotSoundness i
          suzukiDF6D4FixedGridShard135OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 135 k) := by
    simpa [suzukiDF6D4FixedGridShard135OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard135OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 135 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 135) := by
    rw [suzukiDF6D4FixedGridShard135OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 135)
  rw [suzukiDF6D4FixedGridShard135OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard135OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard135OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard135OddDotSoundness i
            suzukiDF6D4FixedGridShard135OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard135OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard135EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard135EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 436) := by
  have h := suzukiDF6D4FixedGridShard135Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard135EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 436)) at h
  exact h

theorem suzukiDF6D4FixedGridShard135EvenFull_eq_live :
    suzukiDF6D4FixedGridShard135EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 436) := by
  have h := suzukiDF6D4FixedGridShard135Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard135EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 436)) at h
  exact h

def suzukiDF6D4FixedGridShard135EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard135EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard135EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard135EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard135EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard135EvenResidualData =
      suzukiDF6D4FixedGridShard135EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard135Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard135EvenResidualData =
    suzukiDF6D4FixedGridShard135EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard135EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard135EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 436 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 436) := by
    rw [suzukiDF6D4FixedGridShard135EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 436
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135EvenDotSoundness i
          suzukiDF6D4FixedGridShard135EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 436) := by
    simpa [suzukiDF6D4FixedGridShard135EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard135EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 436) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 436) := by
    rw [suzukiDF6D4FixedGridShard135EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 436
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard135EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard135EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard135EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard135EvenDotSoundness i
            suzukiDF6D4FixedGridShard135EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard135EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard135OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard135OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 436) := by
  have h := suzukiDF6D4FixedGridShard135Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard135OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 436)) at h
  exact h

theorem suzukiDF6D4FixedGridShard135OddFull_eq_live :
    suzukiDF6D4FixedGridShard135OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 436) := by
  have h := suzukiDF6D4FixedGridShard135Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard135OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 436)) at h
  exact h

def suzukiDF6D4FixedGridShard135OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard135OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard135OddDotSoundness i.val
        suzukiDF6D4FixedGridShard135OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard135OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard135OddResidualData =
      suzukiDF6D4FixedGridShard135OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard135Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard135OddResidualData =
    suzukiDF6D4FixedGridShard135OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard135OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard135OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 436 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 436) := by
    rw [suzukiDF6D4FixedGridShard135OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 436
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135OddDotSoundness i
          suzukiDF6D4FixedGridShard135OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 436) := by
    simpa [suzukiDF6D4FixedGridShard135OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard135OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 436) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard135OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 436) := by
    rw [suzukiDF6D4FixedGridShard135OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 436
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard135OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard135OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard135OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard135OddDotSoundness i
            suzukiDF6D4FixedGridShard135OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard135OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
