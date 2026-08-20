import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard263Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard263Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard263EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard263OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard263EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard263EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 564) := by
  have h := suzukiDF6D4FixedGridShard263Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard263EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 564)) at h
  exact h

theorem suzukiDF6D4FixedGridShard263EvenFull_eq_live :
    suzukiDF6D4FixedGridShard263EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 564) := by
  have h := suzukiDF6D4FixedGridShard263Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard263EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 564)) at h
  exact h

def suzukiDF6D4FixedGridShard263EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard263EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard263EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard263EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard263EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard263EvenResidualData =
      suzukiDF6D4FixedGridShard263EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard263Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard263EvenResidualData =
    suzukiDF6D4FixedGridShard263EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard263EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard263EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 564 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard263EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 564) := by
    rw [suzukiDF6D4FixedGridShard263EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 564
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard263EvenDotSoundness i
          suzukiDF6D4FixedGridShard263EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 564) := by
    simpa [suzukiDF6D4FixedGridShard263EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard263EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 564) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard263EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 564) := by
    rw [suzukiDF6D4FixedGridShard263EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 564
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard263EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard263EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard263EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard263EvenDotSoundness i
            suzukiDF6D4FixedGridShard263EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard263EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard263OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard263OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 564) := by
  have h := suzukiDF6D4FixedGridShard263Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard263OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 564)) at h
  exact h

theorem suzukiDF6D4FixedGridShard263OddFull_eq_live :
    suzukiDF6D4FixedGridShard263OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 564) := by
  have h := suzukiDF6D4FixedGridShard263Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard263OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 564)) at h
  exact h

def suzukiDF6D4FixedGridShard263OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard263OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard263OddDotSoundness i.val
        suzukiDF6D4FixedGridShard263OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard263OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard263OddResidualData =
      suzukiDF6D4FixedGridShard263OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard263Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard263OddResidualData =
    suzukiDF6D4FixedGridShard263OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard263OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard263OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 564 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard263OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 564) := by
    rw [suzukiDF6D4FixedGridShard263OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 564
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard263OddDotSoundness i
          suzukiDF6D4FixedGridShard263OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 564) := by
    simpa [suzukiDF6D4FixedGridShard263OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard263OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 564) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard263OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 564) := by
    rw [suzukiDF6D4FixedGridShard263OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 564
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard263OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard263OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard263OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard263OddDotSoundness i
            suzukiDF6D4FixedGridShard263OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard263OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
