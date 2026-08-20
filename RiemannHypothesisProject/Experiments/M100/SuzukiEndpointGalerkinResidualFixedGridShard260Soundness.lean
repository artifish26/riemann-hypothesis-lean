import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard260Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard260Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard260EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard260OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard260EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard260EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 561) := by
  have h := suzukiDF6D4FixedGridShard260Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard260EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 561)) at h
  exact h

theorem suzukiDF6D4FixedGridShard260EvenFull_eq_live :
    suzukiDF6D4FixedGridShard260EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 561) := by
  have h := suzukiDF6D4FixedGridShard260Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard260EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 561)) at h
  exact h

def suzukiDF6D4FixedGridShard260EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard260EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard260EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard260EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard260EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard260EvenResidualData =
      suzukiDF6D4FixedGridShard260EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard260Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard260EvenResidualData =
    suzukiDF6D4FixedGridShard260EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard260EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard260EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 561 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard260EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 561) := by
    rw [suzukiDF6D4FixedGridShard260EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 561
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard260EvenDotSoundness i
          suzukiDF6D4FixedGridShard260EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 561) := by
    simpa [suzukiDF6D4FixedGridShard260EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard260EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 561) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard260EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 561) := by
    rw [suzukiDF6D4FixedGridShard260EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 561
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard260EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard260EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard260EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard260EvenDotSoundness i
            suzukiDF6D4FixedGridShard260EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard260EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard260OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard260OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 561) := by
  have h := suzukiDF6D4FixedGridShard260Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard260OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 561)) at h
  exact h

theorem suzukiDF6D4FixedGridShard260OddFull_eq_live :
    suzukiDF6D4FixedGridShard260OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 561) := by
  have h := suzukiDF6D4FixedGridShard260Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard260OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 561)) at h
  exact h

def suzukiDF6D4FixedGridShard260OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard260OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard260OddDotSoundness i.val
        suzukiDF6D4FixedGridShard260OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard260OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard260OddResidualData =
      suzukiDF6D4FixedGridShard260OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard260Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard260OddResidualData =
    suzukiDF6D4FixedGridShard260OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard260OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard260OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 561 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard260OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 561) := by
    rw [suzukiDF6D4FixedGridShard260OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 561
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard260OddDotSoundness i
          suzukiDF6D4FixedGridShard260OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 561) := by
    simpa [suzukiDF6D4FixedGridShard260OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard260OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 561) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard260OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 561) := by
    rw [suzukiDF6D4FixedGridShard260OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 561
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard260OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard260OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard260OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard260OddDotSoundness i
            suzukiDF6D4FixedGridShard260OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard260OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
