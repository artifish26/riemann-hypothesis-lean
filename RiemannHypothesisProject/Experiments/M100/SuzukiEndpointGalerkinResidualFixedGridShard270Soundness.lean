import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard270Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard270Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard270EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard270OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard270EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard270EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 571) := by
  have h := suzukiDF6D4FixedGridShard270Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard270EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 571)) at h
  exact h

theorem suzukiDF6D4FixedGridShard270EvenFull_eq_live :
    suzukiDF6D4FixedGridShard270EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 571) := by
  have h := suzukiDF6D4FixedGridShard270Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard270EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 571)) at h
  exact h

def suzukiDF6D4FixedGridShard270EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard270EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard270EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard270EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard270EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard270EvenResidualData =
      suzukiDF6D4FixedGridShard270EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard270Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard270EvenResidualData =
    suzukiDF6D4FixedGridShard270EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard270EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard270EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 571 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard270EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 571) := by
    rw [suzukiDF6D4FixedGridShard270EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 571
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard270EvenDotSoundness i
          suzukiDF6D4FixedGridShard270EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 571) := by
    simpa [suzukiDF6D4FixedGridShard270EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard270EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 571) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard270EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 571) := by
    rw [suzukiDF6D4FixedGridShard270EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 571
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard270EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard270EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard270EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard270EvenDotSoundness i
            suzukiDF6D4FixedGridShard270EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard270EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard270OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard270OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 571) := by
  have h := suzukiDF6D4FixedGridShard270Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard270OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 571)) at h
  exact h

theorem suzukiDF6D4FixedGridShard270OddFull_eq_live :
    suzukiDF6D4FixedGridShard270OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 571) := by
  have h := suzukiDF6D4FixedGridShard270Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard270OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 571)) at h
  exact h

def suzukiDF6D4FixedGridShard270OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard270OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard270OddDotSoundness i.val
        suzukiDF6D4FixedGridShard270OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard270OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard270OddResidualData =
      suzukiDF6D4FixedGridShard270OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard270Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard270OddResidualData =
    suzukiDF6D4FixedGridShard270OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard270OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard270OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 571 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard270OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 571) := by
    rw [suzukiDF6D4FixedGridShard270OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 571
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard270OddDotSoundness i
          suzukiDF6D4FixedGridShard270OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 571) := by
    simpa [suzukiDF6D4FixedGridShard270OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard270OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 571) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard270OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 571) := by
    rw [suzukiDF6D4FixedGridShard270OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 571
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard270OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard270OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard270OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard270OddDotSoundness i
            suzukiDF6D4FixedGridShard270OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard270OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
