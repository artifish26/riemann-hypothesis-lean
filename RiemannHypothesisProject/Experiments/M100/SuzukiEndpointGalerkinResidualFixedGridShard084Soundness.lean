import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard084Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard084Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard084EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard084EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 84 k) := by
  have h := suzukiDF6D4FixedGridShard084Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard084EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 84 k)) at h
  exact h

def suzukiDF6D4FixedGridShard084EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard084EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard084EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard084EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard084EvenComparisonData)

theorem suzukiDF6D4FixedGridShard084EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard084EvenSolveData =
      suzukiDF6D4FixedGridShard084EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard084Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard084EvenSolveData =
    suzukiDF6D4FixedGridShard084EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard084EvenCross_eq_live :
    suzukiDF6D4FixedGridShard084EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 84) := by
  have h := suzukiDF6D4FixedGridShard084Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard084EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 84)) at h
  exact h

theorem suzukiDF6D4FixedGridShard084EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard084EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 84 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 84 k) := by
    rw [suzukiDF6D4FixedGridShard084EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 84 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084EvenDotSoundness i
          suzukiDF6D4FixedGridShard084EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 84 k) := by
    simpa [suzukiDF6D4FixedGridShard084EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard084EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 84 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 84) := by
    rw [suzukiDF6D4FixedGridShard084EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 84)
  rw [suzukiDF6D4FixedGridShard084EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard084EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard084EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard084EvenDotSoundness i
            suzukiDF6D4FixedGridShard084EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard084EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard084OddComparison_eq_live :
    suzukiDF6D4FixedGridShard084OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 84 k) := by
  have h := suzukiDF6D4FixedGridShard084Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard084OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 84 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard084OddCross_eq_live :
    suzukiDF6D4FixedGridShard084OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 84) := by
  have h := suzukiDF6D4FixedGridShard084Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard084OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 84)) at h
  exact h

def suzukiDF6D4FixedGridShard084OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard084OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard084OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard084OddDotSoundness i.val
      suzukiDF6D4FixedGridShard084OddComparisonData)

theorem suzukiDF6D4FixedGridShard084OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard084OddSolveData =
      suzukiDF6D4FixedGridShard084OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard084Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard084OddSolveData =
    suzukiDF6D4FixedGridShard084OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard084OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard084OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 84 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 84 k) := by
    rw [suzukiDF6D4FixedGridShard084OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 84 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084OddDotSoundness i
          suzukiDF6D4FixedGridShard084OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 84 k) := by
    simpa [suzukiDF6D4FixedGridShard084OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard084OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 84 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 84) := by
    rw [suzukiDF6D4FixedGridShard084OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 84)
  rw [suzukiDF6D4FixedGridShard084OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard084OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard084OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard084OddDotSoundness i
            suzukiDF6D4FixedGridShard084OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard084OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard084EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard084EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 385) := by
  have h := suzukiDF6D4FixedGridShard084Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard084EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 385)) at h
  exact h

theorem suzukiDF6D4FixedGridShard084EvenFull_eq_live :
    suzukiDF6D4FixedGridShard084EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 385) := by
  have h := suzukiDF6D4FixedGridShard084Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard084EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 385)) at h
  exact h

def suzukiDF6D4FixedGridShard084EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard084EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard084EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard084EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard084EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard084EvenResidualData =
      suzukiDF6D4FixedGridShard084EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard084Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard084EvenResidualData =
    suzukiDF6D4FixedGridShard084EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard084EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard084EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 385 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 385) := by
    rw [suzukiDF6D4FixedGridShard084EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 385
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084EvenDotSoundness i
          suzukiDF6D4FixedGridShard084EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 385) := by
    simpa [suzukiDF6D4FixedGridShard084EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard084EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 385) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 385) := by
    rw [suzukiDF6D4FixedGridShard084EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 385
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard084EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard084EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard084EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard084EvenDotSoundness i
            suzukiDF6D4FixedGridShard084EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard084EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard084OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard084OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 385) := by
  have h := suzukiDF6D4FixedGridShard084Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard084OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 385)) at h
  exact h

theorem suzukiDF6D4FixedGridShard084OddFull_eq_live :
    suzukiDF6D4FixedGridShard084OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 385) := by
  have h := suzukiDF6D4FixedGridShard084Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard084OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 385)) at h
  exact h

def suzukiDF6D4FixedGridShard084OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard084OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard084OddDotSoundness i.val
        suzukiDF6D4FixedGridShard084OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard084OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard084OddResidualData =
      suzukiDF6D4FixedGridShard084OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard084Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard084OddResidualData =
    suzukiDF6D4FixedGridShard084OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard084OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard084OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 385 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 385) := by
    rw [suzukiDF6D4FixedGridShard084OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 385
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084OddDotSoundness i
          suzukiDF6D4FixedGridShard084OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 385) := by
    simpa [suzukiDF6D4FixedGridShard084OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard084OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 385) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard084OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 385) := by
    rw [suzukiDF6D4FixedGridShard084OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 385
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard084OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard084OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard084OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard084OddDotSoundness i
            suzukiDF6D4FixedGridShard084OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard084OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
