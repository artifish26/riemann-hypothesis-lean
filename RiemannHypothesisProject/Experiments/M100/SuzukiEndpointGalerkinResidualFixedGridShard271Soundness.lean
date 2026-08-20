import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard271Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard271Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard271EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard271OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard271EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard271EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 572) := by
  have h := suzukiDF6D4FixedGridShard271Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard271EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 572)) at h
  exact h

theorem suzukiDF6D4FixedGridShard271EvenFull_eq_live :
    suzukiDF6D4FixedGridShard271EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 572) := by
  have h := suzukiDF6D4FixedGridShard271Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard271EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 572)) at h
  exact h

def suzukiDF6D4FixedGridShard271EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard271EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard271EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard271EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard271EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard271EvenResidualData =
      suzukiDF6D4FixedGridShard271EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard271Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard271EvenResidualData =
    suzukiDF6D4FixedGridShard271EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard271EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard271EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 572 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard271EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 572) := by
    rw [suzukiDF6D4FixedGridShard271EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 572
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard271EvenDotSoundness i
          suzukiDF6D4FixedGridShard271EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 572) := by
    simpa [suzukiDF6D4FixedGridShard271EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard271EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 572) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard271EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 572) := by
    rw [suzukiDF6D4FixedGridShard271EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 572
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard271EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard271EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard271EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard271EvenDotSoundness i
            suzukiDF6D4FixedGridShard271EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard271EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard271OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard271OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 572) := by
  have h := suzukiDF6D4FixedGridShard271Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard271OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 572)) at h
  exact h

theorem suzukiDF6D4FixedGridShard271OddFull_eq_live :
    suzukiDF6D4FixedGridShard271OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 572) := by
  have h := suzukiDF6D4FixedGridShard271Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard271OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 572)) at h
  exact h

def suzukiDF6D4FixedGridShard271OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard271OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard271OddDotSoundness i.val
        suzukiDF6D4FixedGridShard271OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard271OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard271OddResidualData =
      suzukiDF6D4FixedGridShard271OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard271Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard271OddResidualData =
    suzukiDF6D4FixedGridShard271OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard271OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard271OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 572 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard271OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 572) := by
    rw [suzukiDF6D4FixedGridShard271OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 572
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard271OddDotSoundness i
          suzukiDF6D4FixedGridShard271OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 572) := by
    simpa [suzukiDF6D4FixedGridShard271OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard271OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 572) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard271OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 572) := by
    rw [suzukiDF6D4FixedGridShard271OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 572
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard271OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard271OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard271OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard271OddDotSoundness i
            suzukiDF6D4FixedGridShard271OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard271OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
