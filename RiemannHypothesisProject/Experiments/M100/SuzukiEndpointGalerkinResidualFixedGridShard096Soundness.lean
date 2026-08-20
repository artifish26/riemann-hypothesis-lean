import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard096Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard096Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard096EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard096EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 96 k) := by
  have h := suzukiDF6D4FixedGridShard096Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard096EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 96 k)) at h
  exact h

def suzukiDF6D4FixedGridShard096EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard096EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard096EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard096EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard096EvenComparisonData)

theorem suzukiDF6D4FixedGridShard096EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard096EvenSolveData =
      suzukiDF6D4FixedGridShard096EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard096Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard096EvenSolveData =
    suzukiDF6D4FixedGridShard096EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard096EvenCross_eq_live :
    suzukiDF6D4FixedGridShard096EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 96) := by
  have h := suzukiDF6D4FixedGridShard096Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard096EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 96)) at h
  exact h

theorem suzukiDF6D4FixedGridShard096EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard096EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 96 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 96 k) := by
    rw [suzukiDF6D4FixedGridShard096EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 96 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096EvenDotSoundness i
          suzukiDF6D4FixedGridShard096EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 96 k) := by
    simpa [suzukiDF6D4FixedGridShard096EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard096EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 96 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 96) := by
    rw [suzukiDF6D4FixedGridShard096EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 96)
  rw [suzukiDF6D4FixedGridShard096EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard096EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard096EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard096EvenDotSoundness i
            suzukiDF6D4FixedGridShard096EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard096EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard096OddComparison_eq_live :
    suzukiDF6D4FixedGridShard096OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 96 k) := by
  have h := suzukiDF6D4FixedGridShard096Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard096OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 96 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard096OddCross_eq_live :
    suzukiDF6D4FixedGridShard096OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 96) := by
  have h := suzukiDF6D4FixedGridShard096Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard096OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 96)) at h
  exact h

def suzukiDF6D4FixedGridShard096OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard096OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard096OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard096OddDotSoundness i.val
      suzukiDF6D4FixedGridShard096OddComparisonData)

theorem suzukiDF6D4FixedGridShard096OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard096OddSolveData =
      suzukiDF6D4FixedGridShard096OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard096Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard096OddSolveData =
    suzukiDF6D4FixedGridShard096OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard096OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard096OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 96 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 96 k) := by
    rw [suzukiDF6D4FixedGridShard096OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 96 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096OddDotSoundness i
          suzukiDF6D4FixedGridShard096OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 96 k) := by
    simpa [suzukiDF6D4FixedGridShard096OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard096OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 96 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 96) := by
    rw [suzukiDF6D4FixedGridShard096OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 96)
  rw [suzukiDF6D4FixedGridShard096OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard096OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard096OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard096OddDotSoundness i
            suzukiDF6D4FixedGridShard096OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard096OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard096EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard096EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 397) := by
  have h := suzukiDF6D4FixedGridShard096Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard096EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 397)) at h
  exact h

theorem suzukiDF6D4FixedGridShard096EvenFull_eq_live :
    suzukiDF6D4FixedGridShard096EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 397) := by
  have h := suzukiDF6D4FixedGridShard096Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard096EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 397)) at h
  exact h

def suzukiDF6D4FixedGridShard096EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard096EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard096EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard096EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard096EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard096EvenResidualData =
      suzukiDF6D4FixedGridShard096EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard096Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard096EvenResidualData =
    suzukiDF6D4FixedGridShard096EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard096EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard096EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 397 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 397) := by
    rw [suzukiDF6D4FixedGridShard096EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 397
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096EvenDotSoundness i
          suzukiDF6D4FixedGridShard096EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 397) := by
    simpa [suzukiDF6D4FixedGridShard096EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard096EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 397) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 397) := by
    rw [suzukiDF6D4FixedGridShard096EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 397
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard096EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard096EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard096EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard096EvenDotSoundness i
            suzukiDF6D4FixedGridShard096EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard096EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard096OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard096OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 397) := by
  have h := suzukiDF6D4FixedGridShard096Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard096OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 397)) at h
  exact h

theorem suzukiDF6D4FixedGridShard096OddFull_eq_live :
    suzukiDF6D4FixedGridShard096OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 397) := by
  have h := suzukiDF6D4FixedGridShard096Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard096OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 397)) at h
  exact h

def suzukiDF6D4FixedGridShard096OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard096OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard096OddDotSoundness i.val
        suzukiDF6D4FixedGridShard096OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard096OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard096OddResidualData =
      suzukiDF6D4FixedGridShard096OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard096Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard096OddResidualData =
    suzukiDF6D4FixedGridShard096OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard096OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard096OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 397 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 397) := by
    rw [suzukiDF6D4FixedGridShard096OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 397
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096OddDotSoundness i
          suzukiDF6D4FixedGridShard096OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 397) := by
    simpa [suzukiDF6D4FixedGridShard096OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard096OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 397) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard096OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 397) := by
    rw [suzukiDF6D4FixedGridShard096OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 397
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard096OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard096OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard096OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard096OddDotSoundness i
            suzukiDF6D4FixedGridShard096OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard096OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
