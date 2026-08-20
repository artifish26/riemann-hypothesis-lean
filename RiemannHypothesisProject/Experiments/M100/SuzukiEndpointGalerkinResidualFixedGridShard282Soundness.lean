import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard282Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard282Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard282EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard282OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard282EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard282EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 583) := by
  have h := suzukiDF6D4FixedGridShard282Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard282EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 583)) at h
  exact h

theorem suzukiDF6D4FixedGridShard282EvenFull_eq_live :
    suzukiDF6D4FixedGridShard282EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 583) := by
  have h := suzukiDF6D4FixedGridShard282Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard282EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 583)) at h
  exact h

def suzukiDF6D4FixedGridShard282EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard282EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard282EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard282EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard282EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard282EvenResidualData =
      suzukiDF6D4FixedGridShard282EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard282Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard282EvenResidualData =
    suzukiDF6D4FixedGridShard282EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard282EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard282EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 583 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard282EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 583) := by
    rw [suzukiDF6D4FixedGridShard282EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 583
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard282EvenDotSoundness i
          suzukiDF6D4FixedGridShard282EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 583) := by
    simpa [suzukiDF6D4FixedGridShard282EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard282EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 583) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard282EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 583) := by
    rw [suzukiDF6D4FixedGridShard282EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 583
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard282EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard282EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard282EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard282EvenDotSoundness i
            suzukiDF6D4FixedGridShard282EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard282EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard282OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard282OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 583) := by
  have h := suzukiDF6D4FixedGridShard282Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard282OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 583)) at h
  exact h

theorem suzukiDF6D4FixedGridShard282OddFull_eq_live :
    suzukiDF6D4FixedGridShard282OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 583) := by
  have h := suzukiDF6D4FixedGridShard282Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard282OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 583)) at h
  exact h

def suzukiDF6D4FixedGridShard282OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard282OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard282OddDotSoundness i.val
        suzukiDF6D4FixedGridShard282OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard282OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard282OddResidualData =
      suzukiDF6D4FixedGridShard282OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard282Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard282OddResidualData =
    suzukiDF6D4FixedGridShard282OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard282OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard282OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 583 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard282OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 583) := by
    rw [suzukiDF6D4FixedGridShard282OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 583
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard282OddDotSoundness i
          suzukiDF6D4FixedGridShard282OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 583) := by
    simpa [suzukiDF6D4FixedGridShard282OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard282OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 583) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard282OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 583) := by
    rw [suzukiDF6D4FixedGridShard282OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 583
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard282OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard282OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard282OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard282OddDotSoundness i
            suzukiDF6D4FixedGridShard282OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard282OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
