import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard295Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard295Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard295EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard295OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard295EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard295EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 596) := by
  have h := suzukiDF6D4FixedGridShard295Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard295EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 596)) at h
  exact h

theorem suzukiDF6D4FixedGridShard295EvenFull_eq_live :
    suzukiDF6D4FixedGridShard295EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 596) := by
  have h := suzukiDF6D4FixedGridShard295Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard295EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 596)) at h
  exact h

def suzukiDF6D4FixedGridShard295EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard295EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard295EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard295EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard295EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard295EvenResidualData =
      suzukiDF6D4FixedGridShard295EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard295Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard295EvenResidualData =
    suzukiDF6D4FixedGridShard295EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard295EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard295EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 596 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard295EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 596) := by
    rw [suzukiDF6D4FixedGridShard295EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 596
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard295EvenDotSoundness i
          suzukiDF6D4FixedGridShard295EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 596) := by
    simpa [suzukiDF6D4FixedGridShard295EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard295EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 596) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard295EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 596) := by
    rw [suzukiDF6D4FixedGridShard295EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 596
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard295EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard295EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard295EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard295EvenDotSoundness i
            suzukiDF6D4FixedGridShard295EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard295EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard295OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard295OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 596) := by
  have h := suzukiDF6D4FixedGridShard295Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard295OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 596)) at h
  exact h

theorem suzukiDF6D4FixedGridShard295OddFull_eq_live :
    suzukiDF6D4FixedGridShard295OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 596) := by
  have h := suzukiDF6D4FixedGridShard295Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard295OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 596)) at h
  exact h

def suzukiDF6D4FixedGridShard295OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard295OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard295OddDotSoundness i.val
        suzukiDF6D4FixedGridShard295OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard295OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard295OddResidualData =
      suzukiDF6D4FixedGridShard295OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard295Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard295OddResidualData =
    suzukiDF6D4FixedGridShard295OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard295OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard295OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 596 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard295OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 596) := by
    rw [suzukiDF6D4FixedGridShard295OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 596
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard295OddDotSoundness i
          suzukiDF6D4FixedGridShard295OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 596) := by
    simpa [suzukiDF6D4FixedGridShard295OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard295OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 596) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard295OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 596) := by
    rw [suzukiDF6D4FixedGridShard295OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 596
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard295OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard295OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard295OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard295OddDotSoundness i
            suzukiDF6D4FixedGridShard295OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard295OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
