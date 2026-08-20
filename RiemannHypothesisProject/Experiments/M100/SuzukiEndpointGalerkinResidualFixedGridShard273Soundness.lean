import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard273Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard273Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard273EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard273OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard273EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard273EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 574) := by
  have h := suzukiDF6D4FixedGridShard273Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard273EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 574)) at h
  exact h

theorem suzukiDF6D4FixedGridShard273EvenFull_eq_live :
    suzukiDF6D4FixedGridShard273EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 574) := by
  have h := suzukiDF6D4FixedGridShard273Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard273EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 574)) at h
  exact h

def suzukiDF6D4FixedGridShard273EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard273EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard273EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard273EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard273EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard273EvenResidualData =
      suzukiDF6D4FixedGridShard273EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard273Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard273EvenResidualData =
    suzukiDF6D4FixedGridShard273EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard273EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard273EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 574 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard273EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 574) := by
    rw [suzukiDF6D4FixedGridShard273EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 574
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard273EvenDotSoundness i
          suzukiDF6D4FixedGridShard273EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 574) := by
    simpa [suzukiDF6D4FixedGridShard273EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard273EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 574) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard273EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 574) := by
    rw [suzukiDF6D4FixedGridShard273EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 574
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard273EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard273EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard273EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard273EvenDotSoundness i
            suzukiDF6D4FixedGridShard273EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard273EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard273OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard273OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 574) := by
  have h := suzukiDF6D4FixedGridShard273Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard273OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 574)) at h
  exact h

theorem suzukiDF6D4FixedGridShard273OddFull_eq_live :
    suzukiDF6D4FixedGridShard273OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 574) := by
  have h := suzukiDF6D4FixedGridShard273Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard273OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 574)) at h
  exact h

def suzukiDF6D4FixedGridShard273OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard273OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard273OddDotSoundness i.val
        suzukiDF6D4FixedGridShard273OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard273OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard273OddResidualData =
      suzukiDF6D4FixedGridShard273OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard273Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard273OddResidualData =
    suzukiDF6D4FixedGridShard273OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard273OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard273OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 574 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard273OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 574) := by
    rw [suzukiDF6D4FixedGridShard273OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 574
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard273OddDotSoundness i
          suzukiDF6D4FixedGridShard273OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 574) := by
    simpa [suzukiDF6D4FixedGridShard273OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard273OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 574) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard273OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 574) := by
    rw [suzukiDF6D4FixedGridShard273OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 574
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard273OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard273OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard273OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard273OddDotSoundness i
            suzukiDF6D4FixedGridShard273OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard273OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
