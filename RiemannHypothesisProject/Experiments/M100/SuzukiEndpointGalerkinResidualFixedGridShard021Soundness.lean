import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard021Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard021Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard021EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard021EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 21 k) := by
  have h := suzukiDF6D4FixedGridShard021Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard021EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 21 k)) at h
  exact h

def suzukiDF6D4FixedGridShard021EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard021EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard021EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard021EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard021EvenComparisonData)

theorem suzukiDF6D4FixedGridShard021EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard021EvenSolveData =
      suzukiDF6D4FixedGridShard021EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard021Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard021EvenSolveData =
    suzukiDF6D4FixedGridShard021EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard021EvenCross_eq_live :
    suzukiDF6D4FixedGridShard021EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 21) := by
  have h := suzukiDF6D4FixedGridShard021Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard021EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 21)) at h
  exact h

theorem suzukiDF6D4FixedGridShard021EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard021EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 21 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 21 k) := by
    rw [suzukiDF6D4FixedGridShard021EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 21 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021EvenDotSoundness i
          suzukiDF6D4FixedGridShard021EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 21 k) := by
    simpa [suzukiDF6D4FixedGridShard021EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard021EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 21 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 21) := by
    rw [suzukiDF6D4FixedGridShard021EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 21)
  rw [suzukiDF6D4FixedGridShard021EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard021EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard021EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard021EvenDotSoundness i
            suzukiDF6D4FixedGridShard021EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard021EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard021OddComparison_eq_live :
    suzukiDF6D4FixedGridShard021OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 21 k) := by
  have h := suzukiDF6D4FixedGridShard021Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard021OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 21 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard021OddCross_eq_live :
    suzukiDF6D4FixedGridShard021OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 21) := by
  have h := suzukiDF6D4FixedGridShard021Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard021OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 21)) at h
  exact h

def suzukiDF6D4FixedGridShard021OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard021OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard021OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard021OddDotSoundness i.val
      suzukiDF6D4FixedGridShard021OddComparisonData)

theorem suzukiDF6D4FixedGridShard021OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard021OddSolveData =
      suzukiDF6D4FixedGridShard021OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard021Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard021OddSolveData =
    suzukiDF6D4FixedGridShard021OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard021OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard021OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 21 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 21 k) := by
    rw [suzukiDF6D4FixedGridShard021OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 21 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021OddDotSoundness i
          suzukiDF6D4FixedGridShard021OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 21 k) := by
    simpa [suzukiDF6D4FixedGridShard021OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard021OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 21 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 21) := by
    rw [suzukiDF6D4FixedGridShard021OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 21)
  rw [suzukiDF6D4FixedGridShard021OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard021OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard021OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard021OddDotSoundness i
            suzukiDF6D4FixedGridShard021OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard021OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard021EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard021EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 322) := by
  have h := suzukiDF6D4FixedGridShard021Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard021EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 322)) at h
  exact h

theorem suzukiDF6D4FixedGridShard021EvenFull_eq_live :
    suzukiDF6D4FixedGridShard021EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 322) := by
  have h := suzukiDF6D4FixedGridShard021Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard021EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 322)) at h
  exact h

def suzukiDF6D4FixedGridShard021EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard021EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard021EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard021EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard021EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard021EvenResidualData =
      suzukiDF6D4FixedGridShard021EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard021Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard021EvenResidualData =
    suzukiDF6D4FixedGridShard021EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard021EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard021EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 322 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 322) := by
    rw [suzukiDF6D4FixedGridShard021EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 322
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021EvenDotSoundness i
          suzukiDF6D4FixedGridShard021EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 322) := by
    simpa [suzukiDF6D4FixedGridShard021EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard021EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 322) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 322) := by
    rw [suzukiDF6D4FixedGridShard021EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 322
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard021EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard021EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard021EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard021EvenDotSoundness i
            suzukiDF6D4FixedGridShard021EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard021EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard021OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard021OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 322) := by
  have h := suzukiDF6D4FixedGridShard021Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard021OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 322)) at h
  exact h

theorem suzukiDF6D4FixedGridShard021OddFull_eq_live :
    suzukiDF6D4FixedGridShard021OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 322) := by
  have h := suzukiDF6D4FixedGridShard021Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard021OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 322)) at h
  exact h

def suzukiDF6D4FixedGridShard021OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard021OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard021OddDotSoundness i.val
        suzukiDF6D4FixedGridShard021OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard021OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard021OddResidualData =
      suzukiDF6D4FixedGridShard021OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard021Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard021OddResidualData =
    suzukiDF6D4FixedGridShard021OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard021OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard021OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 322 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 322) := by
    rw [suzukiDF6D4FixedGridShard021OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 322
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021OddDotSoundness i
          suzukiDF6D4FixedGridShard021OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 322) := by
    simpa [suzukiDF6D4FixedGridShard021OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard021OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 322) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard021OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 322) := by
    rw [suzukiDF6D4FixedGridShard021OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 322
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard021OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard021OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard021OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard021OddDotSoundness i
            suzukiDF6D4FixedGridShard021OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard021OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
