import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard280Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard280Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard280EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard280OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard280EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard280EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 581) := by
  have h := suzukiDF6D4FixedGridShard280Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard280EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 581)) at h
  exact h

theorem suzukiDF6D4FixedGridShard280EvenFull_eq_live :
    suzukiDF6D4FixedGridShard280EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 581) := by
  have h := suzukiDF6D4FixedGridShard280Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard280EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 581)) at h
  exact h

def suzukiDF6D4FixedGridShard280EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard280EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard280EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard280EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard280EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard280EvenResidualData =
      suzukiDF6D4FixedGridShard280EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard280Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard280EvenResidualData =
    suzukiDF6D4FixedGridShard280EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard280EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard280EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 581 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard280EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 581) := by
    rw [suzukiDF6D4FixedGridShard280EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 581
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard280EvenDotSoundness i
          suzukiDF6D4FixedGridShard280EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 581) := by
    simpa [suzukiDF6D4FixedGridShard280EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard280EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 581) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard280EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 581) := by
    rw [suzukiDF6D4FixedGridShard280EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 581
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard280EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard280EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard280EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard280EvenDotSoundness i
            suzukiDF6D4FixedGridShard280EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard280EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard280OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard280OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 581) := by
  have h := suzukiDF6D4FixedGridShard280Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard280OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 581)) at h
  exact h

theorem suzukiDF6D4FixedGridShard280OddFull_eq_live :
    suzukiDF6D4FixedGridShard280OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 581) := by
  have h := suzukiDF6D4FixedGridShard280Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard280OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 581)) at h
  exact h

def suzukiDF6D4FixedGridShard280OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard280OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard280OddDotSoundness i.val
        suzukiDF6D4FixedGridShard280OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard280OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard280OddResidualData =
      suzukiDF6D4FixedGridShard280OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard280Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard280OddResidualData =
    suzukiDF6D4FixedGridShard280OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard280OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard280OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 581 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard280OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 581) := by
    rw [suzukiDF6D4FixedGridShard280OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 581
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard280OddDotSoundness i
          suzukiDF6D4FixedGridShard280OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 581) := by
    simpa [suzukiDF6D4FixedGridShard280OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard280OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 581) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard280OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 581) := by
    rw [suzukiDF6D4FixedGridShard280OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 581
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard280OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard280OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard280OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard280OddDotSoundness i
            suzukiDF6D4FixedGridShard280OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard280OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
