import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard288Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard288Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard288EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard288OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard288EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard288EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 589) := by
  have h := suzukiDF6D4FixedGridShard288Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard288EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 589)) at h
  exact h

theorem suzukiDF6D4FixedGridShard288EvenFull_eq_live :
    suzukiDF6D4FixedGridShard288EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 589) := by
  have h := suzukiDF6D4FixedGridShard288Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard288EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 589)) at h
  exact h

def suzukiDF6D4FixedGridShard288EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard288EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard288EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard288EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard288EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard288EvenResidualData =
      suzukiDF6D4FixedGridShard288EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard288Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard288EvenResidualData =
    suzukiDF6D4FixedGridShard288EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard288EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard288EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 589 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard288EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 589) := by
    rw [suzukiDF6D4FixedGridShard288EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 589
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard288EvenDotSoundness i
          suzukiDF6D4FixedGridShard288EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 589) := by
    simpa [suzukiDF6D4FixedGridShard288EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard288EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 589) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard288EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 589) := by
    rw [suzukiDF6D4FixedGridShard288EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 589
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard288EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard288EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard288EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard288EvenDotSoundness i
            suzukiDF6D4FixedGridShard288EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard288EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard288OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard288OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 589) := by
  have h := suzukiDF6D4FixedGridShard288Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard288OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 589)) at h
  exact h

theorem suzukiDF6D4FixedGridShard288OddFull_eq_live :
    suzukiDF6D4FixedGridShard288OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 589) := by
  have h := suzukiDF6D4FixedGridShard288Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard288OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 589)) at h
  exact h

def suzukiDF6D4FixedGridShard288OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard288OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard288OddDotSoundness i.val
        suzukiDF6D4FixedGridShard288OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard288OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard288OddResidualData =
      suzukiDF6D4FixedGridShard288OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard288Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard288OddResidualData =
    suzukiDF6D4FixedGridShard288OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard288OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard288OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 589 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard288OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 589) := by
    rw [suzukiDF6D4FixedGridShard288OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 589
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard288OddDotSoundness i
          suzukiDF6D4FixedGridShard288OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 589) := by
    simpa [suzukiDF6D4FixedGridShard288OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard288OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 589) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard288OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 589) := by
    rw [suzukiDF6D4FixedGridShard288OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 589
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard288OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard288OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard288OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard288OddDotSoundness i
            suzukiDF6D4FixedGridShard288OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard288OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
