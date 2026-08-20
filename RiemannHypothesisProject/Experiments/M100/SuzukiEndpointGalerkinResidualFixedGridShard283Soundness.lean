import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard283Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard283Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard283EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard283OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard283EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard283EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 584) := by
  have h := suzukiDF6D4FixedGridShard283Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard283EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 584)) at h
  exact h

theorem suzukiDF6D4FixedGridShard283EvenFull_eq_live :
    suzukiDF6D4FixedGridShard283EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 584) := by
  have h := suzukiDF6D4FixedGridShard283Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard283EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 584)) at h
  exact h

def suzukiDF6D4FixedGridShard283EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard283EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard283EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard283EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard283EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard283EvenResidualData =
      suzukiDF6D4FixedGridShard283EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard283Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard283EvenResidualData =
    suzukiDF6D4FixedGridShard283EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard283EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard283EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 584 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard283EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 584) := by
    rw [suzukiDF6D4FixedGridShard283EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 584
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard283EvenDotSoundness i
          suzukiDF6D4FixedGridShard283EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 584) := by
    simpa [suzukiDF6D4FixedGridShard283EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard283EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 584) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard283EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 584) := by
    rw [suzukiDF6D4FixedGridShard283EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 584
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard283EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard283EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard283EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard283EvenDotSoundness i
            suzukiDF6D4FixedGridShard283EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard283EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard283OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard283OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 584) := by
  have h := suzukiDF6D4FixedGridShard283Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard283OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 584)) at h
  exact h

theorem suzukiDF6D4FixedGridShard283OddFull_eq_live :
    suzukiDF6D4FixedGridShard283OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 584) := by
  have h := suzukiDF6D4FixedGridShard283Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard283OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 584)) at h
  exact h

def suzukiDF6D4FixedGridShard283OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard283OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard283OddDotSoundness i.val
        suzukiDF6D4FixedGridShard283OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard283OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard283OddResidualData =
      suzukiDF6D4FixedGridShard283OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard283Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard283OddResidualData =
    suzukiDF6D4FixedGridShard283OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard283OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard283OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 584 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard283OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 584) := by
    rw [suzukiDF6D4FixedGridShard283OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 584
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard283OddDotSoundness i
          suzukiDF6D4FixedGridShard283OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 584) := by
    simpa [suzukiDF6D4FixedGridShard283OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard283OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 584) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard283OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 584) := by
    rw [suzukiDF6D4FixedGridShard283OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 584
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard283OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard283OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard283OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard283OddDotSoundness i
            suzukiDF6D4FixedGridShard283OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard283OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
