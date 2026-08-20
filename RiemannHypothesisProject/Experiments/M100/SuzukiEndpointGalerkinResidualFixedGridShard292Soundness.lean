import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard292Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard292Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard292EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard292OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard292EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard292EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 593) := by
  have h := suzukiDF6D4FixedGridShard292Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard292EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 593)) at h
  exact h

theorem suzukiDF6D4FixedGridShard292EvenFull_eq_live :
    suzukiDF6D4FixedGridShard292EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 593) := by
  have h := suzukiDF6D4FixedGridShard292Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard292EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 593)) at h
  exact h

def suzukiDF6D4FixedGridShard292EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard292EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard292EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard292EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard292EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard292EvenResidualData =
      suzukiDF6D4FixedGridShard292EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard292Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard292EvenResidualData =
    suzukiDF6D4FixedGridShard292EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard292EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard292EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 593 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard292EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 593) := by
    rw [suzukiDF6D4FixedGridShard292EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 593
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard292EvenDotSoundness i
          suzukiDF6D4FixedGridShard292EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 593) := by
    simpa [suzukiDF6D4FixedGridShard292EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard292EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 593) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard292EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 593) := by
    rw [suzukiDF6D4FixedGridShard292EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 593
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard292EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard292EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard292EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard292EvenDotSoundness i
            suzukiDF6D4FixedGridShard292EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard292EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard292OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard292OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 593) := by
  have h := suzukiDF6D4FixedGridShard292Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard292OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 593)) at h
  exact h

theorem suzukiDF6D4FixedGridShard292OddFull_eq_live :
    suzukiDF6D4FixedGridShard292OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 593) := by
  have h := suzukiDF6D4FixedGridShard292Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard292OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 593)) at h
  exact h

def suzukiDF6D4FixedGridShard292OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard292OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard292OddDotSoundness i.val
        suzukiDF6D4FixedGridShard292OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard292OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard292OddResidualData =
      suzukiDF6D4FixedGridShard292OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard292Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard292OddResidualData =
    suzukiDF6D4FixedGridShard292OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard292OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard292OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 593 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard292OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 593) := by
    rw [suzukiDF6D4FixedGridShard292OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 593
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard292OddDotSoundness i
          suzukiDF6D4FixedGridShard292OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 593) := by
    simpa [suzukiDF6D4FixedGridShard292OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard292OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 593) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard292OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 593) := by
    rw [suzukiDF6D4FixedGridShard292OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 593
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard292OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard292OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard292OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard292OddDotSoundness i
            suzukiDF6D4FixedGridShard292OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard292OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
