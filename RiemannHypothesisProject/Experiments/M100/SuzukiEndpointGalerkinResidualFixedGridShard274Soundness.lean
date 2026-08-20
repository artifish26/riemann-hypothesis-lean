import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard274Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard274Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard274EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard274OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard274EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard274EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 575) := by
  have h := suzukiDF6D4FixedGridShard274Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard274EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 575)) at h
  exact h

theorem suzukiDF6D4FixedGridShard274EvenFull_eq_live :
    suzukiDF6D4FixedGridShard274EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 575) := by
  have h := suzukiDF6D4FixedGridShard274Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard274EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 575)) at h
  exact h

def suzukiDF6D4FixedGridShard274EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard274EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard274EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard274EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard274EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard274EvenResidualData =
      suzukiDF6D4FixedGridShard274EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard274Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard274EvenResidualData =
    suzukiDF6D4FixedGridShard274EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard274EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard274EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 575 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard274EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 575) := by
    rw [suzukiDF6D4FixedGridShard274EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 575
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard274EvenDotSoundness i
          suzukiDF6D4FixedGridShard274EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 575) := by
    simpa [suzukiDF6D4FixedGridShard274EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard274EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 575) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard274EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 575) := by
    rw [suzukiDF6D4FixedGridShard274EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 575
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard274EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard274EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard274EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard274EvenDotSoundness i
            suzukiDF6D4FixedGridShard274EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard274EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard274OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard274OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 575) := by
  have h := suzukiDF6D4FixedGridShard274Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard274OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 575)) at h
  exact h

theorem suzukiDF6D4FixedGridShard274OddFull_eq_live :
    suzukiDF6D4FixedGridShard274OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 575) := by
  have h := suzukiDF6D4FixedGridShard274Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard274OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 575)) at h
  exact h

def suzukiDF6D4FixedGridShard274OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard274OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard274OddDotSoundness i.val
        suzukiDF6D4FixedGridShard274OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard274OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard274OddResidualData =
      suzukiDF6D4FixedGridShard274OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard274Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard274OddResidualData =
    suzukiDF6D4FixedGridShard274OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard274OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard274OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 575 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard274OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 575) := by
    rw [suzukiDF6D4FixedGridShard274OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 575
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard274OddDotSoundness i
          suzukiDF6D4FixedGridShard274OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 575) := by
    simpa [suzukiDF6D4FixedGridShard274OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard274OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 575) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard274OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 575) := by
    rw [suzukiDF6D4FixedGridShard274OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 575
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard274OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard274OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard274OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard274OddDotSoundness i
            suzukiDF6D4FixedGridShard274OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard274OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
