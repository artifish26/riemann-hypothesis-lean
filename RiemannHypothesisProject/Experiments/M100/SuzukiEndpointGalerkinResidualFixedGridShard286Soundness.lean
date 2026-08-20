import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard286Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard286Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard286EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard286OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard286EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard286EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 587) := by
  have h := suzukiDF6D4FixedGridShard286Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard286EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 587)) at h
  exact h

theorem suzukiDF6D4FixedGridShard286EvenFull_eq_live :
    suzukiDF6D4FixedGridShard286EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 587) := by
  have h := suzukiDF6D4FixedGridShard286Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard286EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 587)) at h
  exact h

def suzukiDF6D4FixedGridShard286EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard286EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard286EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard286EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard286EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard286EvenResidualData =
      suzukiDF6D4FixedGridShard286EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard286Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard286EvenResidualData =
    suzukiDF6D4FixedGridShard286EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard286EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard286EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 587 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard286EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 587) := by
    rw [suzukiDF6D4FixedGridShard286EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 587
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard286EvenDotSoundness i
          suzukiDF6D4FixedGridShard286EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 587) := by
    simpa [suzukiDF6D4FixedGridShard286EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard286EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 587) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard286EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 587) := by
    rw [suzukiDF6D4FixedGridShard286EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 587
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard286EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard286EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard286EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard286EvenDotSoundness i
            suzukiDF6D4FixedGridShard286EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard286EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard286OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard286OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 587) := by
  have h := suzukiDF6D4FixedGridShard286Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard286OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 587)) at h
  exact h

theorem suzukiDF6D4FixedGridShard286OddFull_eq_live :
    suzukiDF6D4FixedGridShard286OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 587) := by
  have h := suzukiDF6D4FixedGridShard286Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard286OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 587)) at h
  exact h

def suzukiDF6D4FixedGridShard286OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard286OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard286OddDotSoundness i.val
        suzukiDF6D4FixedGridShard286OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard286OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard286OddResidualData =
      suzukiDF6D4FixedGridShard286OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard286Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard286OddResidualData =
    suzukiDF6D4FixedGridShard286OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard286OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard286OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 587 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard286OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 587) := by
    rw [suzukiDF6D4FixedGridShard286OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 587
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard286OddDotSoundness i
          suzukiDF6D4FixedGridShard286OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 587) := by
    simpa [suzukiDF6D4FixedGridShard286OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard286OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 587) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard286OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 587) := by
    rw [suzukiDF6D4FixedGridShard286OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 587
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard286OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard286OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard286OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard286OddDotSoundness i
            suzukiDF6D4FixedGridShard286OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard286OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
