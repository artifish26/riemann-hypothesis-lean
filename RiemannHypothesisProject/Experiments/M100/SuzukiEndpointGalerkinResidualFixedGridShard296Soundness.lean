import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard296Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard296Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard296EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard296OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard296EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard296EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 597) := by
  have h := suzukiDF6D4FixedGridShard296Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard296EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 597)) at h
  exact h

theorem suzukiDF6D4FixedGridShard296EvenFull_eq_live :
    suzukiDF6D4FixedGridShard296EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 597) := by
  have h := suzukiDF6D4FixedGridShard296Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard296EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 597)) at h
  exact h

def suzukiDF6D4FixedGridShard296EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard296EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard296EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard296EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard296EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard296EvenResidualData =
      suzukiDF6D4FixedGridShard296EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard296Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard296EvenResidualData =
    suzukiDF6D4FixedGridShard296EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard296EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard296EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 597 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard296EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 597) := by
    rw [suzukiDF6D4FixedGridShard296EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 597
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard296EvenDotSoundness i
          suzukiDF6D4FixedGridShard296EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 597) := by
    simpa [suzukiDF6D4FixedGridShard296EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard296EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 597) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard296EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 597) := by
    rw [suzukiDF6D4FixedGridShard296EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 597
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard296EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard296EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard296EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard296EvenDotSoundness i
            suzukiDF6D4FixedGridShard296EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard296EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard296OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard296OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 597) := by
  have h := suzukiDF6D4FixedGridShard296Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard296OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 597)) at h
  exact h

theorem suzukiDF6D4FixedGridShard296OddFull_eq_live :
    suzukiDF6D4FixedGridShard296OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 597) := by
  have h := suzukiDF6D4FixedGridShard296Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard296OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 597)) at h
  exact h

def suzukiDF6D4FixedGridShard296OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard296OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard296OddDotSoundness i.val
        suzukiDF6D4FixedGridShard296OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard296OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard296OddResidualData =
      suzukiDF6D4FixedGridShard296OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard296Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard296OddResidualData =
    suzukiDF6D4FixedGridShard296OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard296OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard296OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 597 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard296OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 597) := by
    rw [suzukiDF6D4FixedGridShard296OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 597
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard296OddDotSoundness i
          suzukiDF6D4FixedGridShard296OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 597) := by
    simpa [suzukiDF6D4FixedGridShard296OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard296OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 597) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard296OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 597) := by
    rw [suzukiDF6D4FixedGridShard296OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 597
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard296OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard296OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard296OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard296OddDotSoundness i
            suzukiDF6D4FixedGridShard296OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard296OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
