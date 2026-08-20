import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard269Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard269Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard269EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard269OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard269EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard269EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 570) := by
  have h := suzukiDF6D4FixedGridShard269Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard269EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 570)) at h
  exact h

theorem suzukiDF6D4FixedGridShard269EvenFull_eq_live :
    suzukiDF6D4FixedGridShard269EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 570) := by
  have h := suzukiDF6D4FixedGridShard269Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard269EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 570)) at h
  exact h

def suzukiDF6D4FixedGridShard269EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard269EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard269EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard269EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard269EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard269EvenResidualData =
      suzukiDF6D4FixedGridShard269EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard269Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard269EvenResidualData =
    suzukiDF6D4FixedGridShard269EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard269EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard269EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 570 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard269EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 570) := by
    rw [suzukiDF6D4FixedGridShard269EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 570
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard269EvenDotSoundness i
          suzukiDF6D4FixedGridShard269EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 570) := by
    simpa [suzukiDF6D4FixedGridShard269EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard269EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 570) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard269EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 570) := by
    rw [suzukiDF6D4FixedGridShard269EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 570
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard269EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard269EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard269EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard269EvenDotSoundness i
            suzukiDF6D4FixedGridShard269EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard269EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard269OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard269OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 570) := by
  have h := suzukiDF6D4FixedGridShard269Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard269OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 570)) at h
  exact h

theorem suzukiDF6D4FixedGridShard269OddFull_eq_live :
    suzukiDF6D4FixedGridShard269OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 570) := by
  have h := suzukiDF6D4FixedGridShard269Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard269OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 570)) at h
  exact h

def suzukiDF6D4FixedGridShard269OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard269OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard269OddDotSoundness i.val
        suzukiDF6D4FixedGridShard269OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard269OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard269OddResidualData =
      suzukiDF6D4FixedGridShard269OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard269Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard269OddResidualData =
    suzukiDF6D4FixedGridShard269OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard269OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard269OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 570 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard269OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 570) := by
    rw [suzukiDF6D4FixedGridShard269OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 570
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard269OddDotSoundness i
          suzukiDF6D4FixedGridShard269OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 570) := by
    simpa [suzukiDF6D4FixedGridShard269OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard269OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 570) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard269OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 570) := by
    rw [suzukiDF6D4FixedGridShard269OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 570
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard269OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard269OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard269OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard269OddDotSoundness i
            suzukiDF6D4FixedGridShard269OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard269OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
