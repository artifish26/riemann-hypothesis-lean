import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard232Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard232Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard232EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard232EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 232 k) := by
  have h := suzukiDF6D4FixedGridShard232Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard232EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 232 k)) at h
  exact h

def suzukiDF6D4FixedGridShard232EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard232EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard232EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard232EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard232EvenComparisonData)

theorem suzukiDF6D4FixedGridShard232EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard232EvenSolveData =
      suzukiDF6D4FixedGridShard232EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard232Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard232EvenSolveData =
    suzukiDF6D4FixedGridShard232EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard232EvenCross_eq_live :
    suzukiDF6D4FixedGridShard232EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 232) := by
  have h := suzukiDF6D4FixedGridShard232Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard232EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 232)) at h
  exact h

theorem suzukiDF6D4FixedGridShard232EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard232EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 232 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 232 k) := by
    rw [suzukiDF6D4FixedGridShard232EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 232 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232EvenDotSoundness i
          suzukiDF6D4FixedGridShard232EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 232 k) := by
    simpa [suzukiDF6D4FixedGridShard232EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard232EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 232 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 232) := by
    rw [suzukiDF6D4FixedGridShard232EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 232)
  rw [suzukiDF6D4FixedGridShard232EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard232EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard232EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard232EvenDotSoundness i
            suzukiDF6D4FixedGridShard232EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard232EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard232OddComparison_eq_live :
    suzukiDF6D4FixedGridShard232OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 232 k) := by
  have h := suzukiDF6D4FixedGridShard232Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard232OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 232 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard232OddCross_eq_live :
    suzukiDF6D4FixedGridShard232OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 232) := by
  have h := suzukiDF6D4FixedGridShard232Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard232OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 232)) at h
  exact h

def suzukiDF6D4FixedGridShard232OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard232OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard232OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard232OddDotSoundness i.val
      suzukiDF6D4FixedGridShard232OddComparisonData)

theorem suzukiDF6D4FixedGridShard232OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard232OddSolveData =
      suzukiDF6D4FixedGridShard232OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard232Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard232OddSolveData =
    suzukiDF6D4FixedGridShard232OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard232OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard232OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 232 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 232 k) := by
    rw [suzukiDF6D4FixedGridShard232OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 232 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232OddDotSoundness i
          suzukiDF6D4FixedGridShard232OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 232 k) := by
    simpa [suzukiDF6D4FixedGridShard232OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard232OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 232 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 232) := by
    rw [suzukiDF6D4FixedGridShard232OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 232)
  rw [suzukiDF6D4FixedGridShard232OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard232OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard232OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard232OddDotSoundness i
            suzukiDF6D4FixedGridShard232OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard232OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard232EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard232EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 533) := by
  have h := suzukiDF6D4FixedGridShard232Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard232EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 533)) at h
  exact h

theorem suzukiDF6D4FixedGridShard232EvenFull_eq_live :
    suzukiDF6D4FixedGridShard232EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 533) := by
  have h := suzukiDF6D4FixedGridShard232Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard232EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 533)) at h
  exact h

def suzukiDF6D4FixedGridShard232EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard232EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard232EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard232EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard232EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard232EvenResidualData =
      suzukiDF6D4FixedGridShard232EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard232Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard232EvenResidualData =
    suzukiDF6D4FixedGridShard232EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard232EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard232EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 533 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 533) := by
    rw [suzukiDF6D4FixedGridShard232EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 533
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232EvenDotSoundness i
          suzukiDF6D4FixedGridShard232EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 533) := by
    simpa [suzukiDF6D4FixedGridShard232EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard232EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 533) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 533) := by
    rw [suzukiDF6D4FixedGridShard232EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 533
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard232EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard232EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard232EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard232EvenDotSoundness i
            suzukiDF6D4FixedGridShard232EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard232EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard232OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard232OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 533) := by
  have h := suzukiDF6D4FixedGridShard232Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard232OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 533)) at h
  exact h

theorem suzukiDF6D4FixedGridShard232OddFull_eq_live :
    suzukiDF6D4FixedGridShard232OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 533) := by
  have h := suzukiDF6D4FixedGridShard232Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard232OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 533)) at h
  exact h

def suzukiDF6D4FixedGridShard232OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard232OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard232OddDotSoundness i.val
        suzukiDF6D4FixedGridShard232OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard232OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard232OddResidualData =
      suzukiDF6D4FixedGridShard232OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard232Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard232OddResidualData =
    suzukiDF6D4FixedGridShard232OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard232OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard232OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 533 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 533) := by
    rw [suzukiDF6D4FixedGridShard232OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 533
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232OddDotSoundness i
          suzukiDF6D4FixedGridShard232OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 533) := by
    simpa [suzukiDF6D4FixedGridShard232OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard232OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 533) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard232OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 533) := by
    rw [suzukiDF6D4FixedGridShard232OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 533
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard232OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard232OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard232OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard232OddDotSoundness i
            suzukiDF6D4FixedGridShard232OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard232OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
