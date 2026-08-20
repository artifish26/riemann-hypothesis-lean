import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard067Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard067Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard067EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard067EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 67 k) := by
  have h := suzukiDF6D4FixedGridShard067Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard067EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 67 k)) at h
  exact h

def suzukiDF6D4FixedGridShard067EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard067EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard067EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard067EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard067EvenComparisonData)

theorem suzukiDF6D4FixedGridShard067EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard067EvenSolveData =
      suzukiDF6D4FixedGridShard067EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard067Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard067EvenSolveData =
    suzukiDF6D4FixedGridShard067EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard067EvenCross_eq_live :
    suzukiDF6D4FixedGridShard067EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 67) := by
  have h := suzukiDF6D4FixedGridShard067Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard067EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 67)) at h
  exact h

theorem suzukiDF6D4FixedGridShard067EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard067EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 67 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 67 k) := by
    rw [suzukiDF6D4FixedGridShard067EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 67 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067EvenDotSoundness i
          suzukiDF6D4FixedGridShard067EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 67 k) := by
    simpa [suzukiDF6D4FixedGridShard067EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard067EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 67 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 67) := by
    rw [suzukiDF6D4FixedGridShard067EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 67)
  rw [suzukiDF6D4FixedGridShard067EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard067EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard067EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard067EvenDotSoundness i
            suzukiDF6D4FixedGridShard067EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard067EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard067OddComparison_eq_live :
    suzukiDF6D4FixedGridShard067OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 67 k) := by
  have h := suzukiDF6D4FixedGridShard067Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard067OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 67 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard067OddCross_eq_live :
    suzukiDF6D4FixedGridShard067OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 67) := by
  have h := suzukiDF6D4FixedGridShard067Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard067OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 67)) at h
  exact h

def suzukiDF6D4FixedGridShard067OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard067OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard067OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard067OddDotSoundness i.val
      suzukiDF6D4FixedGridShard067OddComparisonData)

theorem suzukiDF6D4FixedGridShard067OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard067OddSolveData =
      suzukiDF6D4FixedGridShard067OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard067Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard067OddSolveData =
    suzukiDF6D4FixedGridShard067OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard067OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard067OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 67 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 67 k) := by
    rw [suzukiDF6D4FixedGridShard067OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 67 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067OddDotSoundness i
          suzukiDF6D4FixedGridShard067OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 67 k) := by
    simpa [suzukiDF6D4FixedGridShard067OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard067OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 67 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 67) := by
    rw [suzukiDF6D4FixedGridShard067OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 67)
  rw [suzukiDF6D4FixedGridShard067OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard067OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard067OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard067OddDotSoundness i
            suzukiDF6D4FixedGridShard067OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard067OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard067EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard067EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 368) := by
  have h := suzukiDF6D4FixedGridShard067Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard067EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 368)) at h
  exact h

theorem suzukiDF6D4FixedGridShard067EvenFull_eq_live :
    suzukiDF6D4FixedGridShard067EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 368) := by
  have h := suzukiDF6D4FixedGridShard067Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard067EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 368)) at h
  exact h

def suzukiDF6D4FixedGridShard067EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard067EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard067EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard067EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard067EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard067EvenResidualData =
      suzukiDF6D4FixedGridShard067EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard067Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard067EvenResidualData =
    suzukiDF6D4FixedGridShard067EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard067EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard067EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 368 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 368) := by
    rw [suzukiDF6D4FixedGridShard067EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 368
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067EvenDotSoundness i
          suzukiDF6D4FixedGridShard067EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 368) := by
    simpa [suzukiDF6D4FixedGridShard067EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard067EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 368) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 368) := by
    rw [suzukiDF6D4FixedGridShard067EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 368
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard067EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard067EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard067EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard067EvenDotSoundness i
            suzukiDF6D4FixedGridShard067EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard067EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard067OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard067OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 368) := by
  have h := suzukiDF6D4FixedGridShard067Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard067OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 368)) at h
  exact h

theorem suzukiDF6D4FixedGridShard067OddFull_eq_live :
    suzukiDF6D4FixedGridShard067OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 368) := by
  have h := suzukiDF6D4FixedGridShard067Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard067OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 368)) at h
  exact h

def suzukiDF6D4FixedGridShard067OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard067OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard067OddDotSoundness i.val
        suzukiDF6D4FixedGridShard067OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard067OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard067OddResidualData =
      suzukiDF6D4FixedGridShard067OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard067Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard067OddResidualData =
    suzukiDF6D4FixedGridShard067OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard067OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard067OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 368 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 368) := by
    rw [suzukiDF6D4FixedGridShard067OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 368
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067OddDotSoundness i
          suzukiDF6D4FixedGridShard067OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 368) := by
    simpa [suzukiDF6D4FixedGridShard067OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard067OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 368) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard067OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 368) := by
    rw [suzukiDF6D4FixedGridShard067OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 368
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard067OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard067OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard067OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard067OddDotSoundness i
            suzukiDF6D4FixedGridShard067OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard067OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
