import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard272Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard272Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard272EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard272OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard272EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard272EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 573) := by
  have h := suzukiDF6D4FixedGridShard272Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard272EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 573)) at h
  exact h

theorem suzukiDF6D4FixedGridShard272EvenFull_eq_live :
    suzukiDF6D4FixedGridShard272EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 573) := by
  have h := suzukiDF6D4FixedGridShard272Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard272EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 573)) at h
  exact h

def suzukiDF6D4FixedGridShard272EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard272EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard272EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard272EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard272EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard272EvenResidualData =
      suzukiDF6D4FixedGridShard272EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard272Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard272EvenResidualData =
    suzukiDF6D4FixedGridShard272EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard272EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard272EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 573 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard272EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 573) := by
    rw [suzukiDF6D4FixedGridShard272EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 573
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard272EvenDotSoundness i
          suzukiDF6D4FixedGridShard272EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 573) := by
    simpa [suzukiDF6D4FixedGridShard272EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard272EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 573) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard272EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 573) := by
    rw [suzukiDF6D4FixedGridShard272EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 573
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard272EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard272EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard272EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard272EvenDotSoundness i
            suzukiDF6D4FixedGridShard272EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard272EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard272OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard272OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 573) := by
  have h := suzukiDF6D4FixedGridShard272Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard272OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 573)) at h
  exact h

theorem suzukiDF6D4FixedGridShard272OddFull_eq_live :
    suzukiDF6D4FixedGridShard272OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 573) := by
  have h := suzukiDF6D4FixedGridShard272Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard272OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 573)) at h
  exact h

def suzukiDF6D4FixedGridShard272OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard272OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard272OddDotSoundness i.val
        suzukiDF6D4FixedGridShard272OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard272OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard272OddResidualData =
      suzukiDF6D4FixedGridShard272OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard272Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard272OddResidualData =
    suzukiDF6D4FixedGridShard272OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard272OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard272OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 573 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard272OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 573) := by
    rw [suzukiDF6D4FixedGridShard272OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 573
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard272OddDotSoundness i
          suzukiDF6D4FixedGridShard272OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 573) := by
    simpa [suzukiDF6D4FixedGridShard272OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard272OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 573) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard272OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 573) := by
    rw [suzukiDF6D4FixedGridShard272OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 573
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard272OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard272OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard272OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard272OddDotSoundness i
            suzukiDF6D4FixedGridShard272OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard272OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
