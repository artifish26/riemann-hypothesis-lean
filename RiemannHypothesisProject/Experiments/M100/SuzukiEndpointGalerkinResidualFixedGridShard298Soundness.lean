import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard298Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard298Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard298EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard298OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard298EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard298EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 599) := by
  have h := suzukiDF6D4FixedGridShard298Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard298EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 599)) at h
  exact h

theorem suzukiDF6D4FixedGridShard298EvenFull_eq_live :
    suzukiDF6D4FixedGridShard298EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 599) := by
  have h := suzukiDF6D4FixedGridShard298Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard298EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 599)) at h
  exact h

def suzukiDF6D4FixedGridShard298EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard298EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard298EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard298EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard298EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard298EvenResidualData =
      suzukiDF6D4FixedGridShard298EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard298Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard298EvenResidualData =
    suzukiDF6D4FixedGridShard298EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard298EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard298EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 599 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard298EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 599) := by
    rw [suzukiDF6D4FixedGridShard298EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 599
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard298EvenDotSoundness i
          suzukiDF6D4FixedGridShard298EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 599) := by
    simpa [suzukiDF6D4FixedGridShard298EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard298EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 599) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard298EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 599) := by
    rw [suzukiDF6D4FixedGridShard298EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 599
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard298EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard298EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard298EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard298EvenDotSoundness i
            suzukiDF6D4FixedGridShard298EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard298EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard298OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard298OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 599) := by
  have h := suzukiDF6D4FixedGridShard298Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard298OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 599)) at h
  exact h

theorem suzukiDF6D4FixedGridShard298OddFull_eq_live :
    suzukiDF6D4FixedGridShard298OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 599) := by
  have h := suzukiDF6D4FixedGridShard298Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard298OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 599)) at h
  exact h

def suzukiDF6D4FixedGridShard298OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard298OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard298OddDotSoundness i.val
        suzukiDF6D4FixedGridShard298OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard298OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard298OddResidualData =
      suzukiDF6D4FixedGridShard298OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard298Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard298OddResidualData =
    suzukiDF6D4FixedGridShard298OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard298OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard298OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 599 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard298OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 599) := by
    rw [suzukiDF6D4FixedGridShard298OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 599
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard298OddDotSoundness i
          suzukiDF6D4FixedGridShard298OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 599) := by
    simpa [suzukiDF6D4FixedGridShard298OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard298OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 599) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard298OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 599) := by
    rw [suzukiDF6D4FixedGridShard298OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 599
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard298OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard298OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard298OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard298OddDotSoundness i
            suzukiDF6D4FixedGridShard298OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard298OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
