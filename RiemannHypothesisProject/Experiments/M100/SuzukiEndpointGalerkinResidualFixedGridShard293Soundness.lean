import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard293Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard293Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard293EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard293OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard293EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard293EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 594) := by
  have h := suzukiDF6D4FixedGridShard293Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard293EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 594)) at h
  exact h

theorem suzukiDF6D4FixedGridShard293EvenFull_eq_live :
    suzukiDF6D4FixedGridShard293EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 594) := by
  have h := suzukiDF6D4FixedGridShard293Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard293EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 594)) at h
  exact h

def suzukiDF6D4FixedGridShard293EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard293EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard293EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard293EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard293EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard293EvenResidualData =
      suzukiDF6D4FixedGridShard293EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard293Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard293EvenResidualData =
    suzukiDF6D4FixedGridShard293EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard293EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard293EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 594 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard293EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 594) := by
    rw [suzukiDF6D4FixedGridShard293EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 594
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard293EvenDotSoundness i
          suzukiDF6D4FixedGridShard293EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 594) := by
    simpa [suzukiDF6D4FixedGridShard293EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard293EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 594) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard293EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 594) := by
    rw [suzukiDF6D4FixedGridShard293EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 594
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard293EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard293EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard293EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard293EvenDotSoundness i
            suzukiDF6D4FixedGridShard293EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard293EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard293OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard293OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 594) := by
  have h := suzukiDF6D4FixedGridShard293Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard293OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 594)) at h
  exact h

theorem suzukiDF6D4FixedGridShard293OddFull_eq_live :
    suzukiDF6D4FixedGridShard293OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 594) := by
  have h := suzukiDF6D4FixedGridShard293Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard293OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 594)) at h
  exact h

def suzukiDF6D4FixedGridShard293OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard293OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard293OddDotSoundness i.val
        suzukiDF6D4FixedGridShard293OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard293OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard293OddResidualData =
      suzukiDF6D4FixedGridShard293OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard293Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard293OddResidualData =
    suzukiDF6D4FixedGridShard293OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard293OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard293OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 594 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard293OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 594) := by
    rw [suzukiDF6D4FixedGridShard293OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 594
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard293OddDotSoundness i
          suzukiDF6D4FixedGridShard293OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 594) := by
    simpa [suzukiDF6D4FixedGridShard293OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard293OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 594) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard293OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 594) := by
    rw [suzukiDF6D4FixedGridShard293OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 594
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard293OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard293OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard293OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard293OddDotSoundness i
            suzukiDF6D4FixedGridShard293OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard293OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
