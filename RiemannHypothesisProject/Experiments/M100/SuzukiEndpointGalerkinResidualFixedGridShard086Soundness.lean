import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard086Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard086Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard086EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard086EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 86 k) := by
  have h := suzukiDF6D4FixedGridShard086Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard086EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 86 k)) at h
  exact h

def suzukiDF6D4FixedGridShard086EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard086EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard086EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard086EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard086EvenComparisonData)

theorem suzukiDF6D4FixedGridShard086EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard086EvenSolveData =
      suzukiDF6D4FixedGridShard086EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard086Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard086EvenSolveData =
    suzukiDF6D4FixedGridShard086EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard086EvenCross_eq_live :
    suzukiDF6D4FixedGridShard086EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 86) := by
  have h := suzukiDF6D4FixedGridShard086Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard086EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 86)) at h
  exact h

theorem suzukiDF6D4FixedGridShard086EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard086EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 86 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 86 k) := by
    rw [suzukiDF6D4FixedGridShard086EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 86 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086EvenDotSoundness i
          suzukiDF6D4FixedGridShard086EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 86 k) := by
    simpa [suzukiDF6D4FixedGridShard086EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard086EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 86 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 86) := by
    rw [suzukiDF6D4FixedGridShard086EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 86)
  rw [suzukiDF6D4FixedGridShard086EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard086EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard086EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard086EvenDotSoundness i
            suzukiDF6D4FixedGridShard086EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard086EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard086OddComparison_eq_live :
    suzukiDF6D4FixedGridShard086OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 86 k) := by
  have h := suzukiDF6D4FixedGridShard086Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard086OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 86 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard086OddCross_eq_live :
    suzukiDF6D4FixedGridShard086OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 86) := by
  have h := suzukiDF6D4FixedGridShard086Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard086OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 86)) at h
  exact h

def suzukiDF6D4FixedGridShard086OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard086OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard086OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard086OddDotSoundness i.val
      suzukiDF6D4FixedGridShard086OddComparisonData)

theorem suzukiDF6D4FixedGridShard086OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard086OddSolveData =
      suzukiDF6D4FixedGridShard086OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard086Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard086OddSolveData =
    suzukiDF6D4FixedGridShard086OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard086OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard086OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 86 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 86 k) := by
    rw [suzukiDF6D4FixedGridShard086OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 86 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086OddDotSoundness i
          suzukiDF6D4FixedGridShard086OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 86 k) := by
    simpa [suzukiDF6D4FixedGridShard086OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard086OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 86 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 86) := by
    rw [suzukiDF6D4FixedGridShard086OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 86)
  rw [suzukiDF6D4FixedGridShard086OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard086OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard086OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard086OddDotSoundness i
            suzukiDF6D4FixedGridShard086OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard086OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard086EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard086EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 387) := by
  have h := suzukiDF6D4FixedGridShard086Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard086EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 387)) at h
  exact h

theorem suzukiDF6D4FixedGridShard086EvenFull_eq_live :
    suzukiDF6D4FixedGridShard086EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 387) := by
  have h := suzukiDF6D4FixedGridShard086Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard086EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 387)) at h
  exact h

def suzukiDF6D4FixedGridShard086EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard086EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard086EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard086EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard086EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard086EvenResidualData =
      suzukiDF6D4FixedGridShard086EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard086Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard086EvenResidualData =
    suzukiDF6D4FixedGridShard086EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard086EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard086EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 387 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 387) := by
    rw [suzukiDF6D4FixedGridShard086EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 387
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086EvenDotSoundness i
          suzukiDF6D4FixedGridShard086EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 387) := by
    simpa [suzukiDF6D4FixedGridShard086EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard086EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 387) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 387) := by
    rw [suzukiDF6D4FixedGridShard086EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 387
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard086EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard086EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard086EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard086EvenDotSoundness i
            suzukiDF6D4FixedGridShard086EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard086EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard086OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard086OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 387) := by
  have h := suzukiDF6D4FixedGridShard086Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard086OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 387)) at h
  exact h

theorem suzukiDF6D4FixedGridShard086OddFull_eq_live :
    suzukiDF6D4FixedGridShard086OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 387) := by
  have h := suzukiDF6D4FixedGridShard086Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard086OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 387)) at h
  exact h

def suzukiDF6D4FixedGridShard086OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard086OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard086OddDotSoundness i.val
        suzukiDF6D4FixedGridShard086OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard086OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard086OddResidualData =
      suzukiDF6D4FixedGridShard086OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard086Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard086OddResidualData =
    suzukiDF6D4FixedGridShard086OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard086OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard086OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 387 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 387) := by
    rw [suzukiDF6D4FixedGridShard086OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 387
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086OddDotSoundness i
          suzukiDF6D4FixedGridShard086OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 387) := by
    simpa [suzukiDF6D4FixedGridShard086OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard086OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 387) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard086OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 387) := by
    rw [suzukiDF6D4FixedGridShard086OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 387
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard086OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard086OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard086OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard086OddDotSoundness i
            suzukiDF6D4FixedGridShard086OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard086OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
