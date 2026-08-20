import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard290Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard290Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard290EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard290OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard290EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard290EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 591) := by
  have h := suzukiDF6D4FixedGridShard290Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard290EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 591)) at h
  exact h

theorem suzukiDF6D4FixedGridShard290EvenFull_eq_live :
    suzukiDF6D4FixedGridShard290EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 591) := by
  have h := suzukiDF6D4FixedGridShard290Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard290EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 591)) at h
  exact h

def suzukiDF6D4FixedGridShard290EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard290EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard290EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard290EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard290EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard290EvenResidualData =
      suzukiDF6D4FixedGridShard290EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard290Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard290EvenResidualData =
    suzukiDF6D4FixedGridShard290EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard290EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard290EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 591 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard290EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 591) := by
    rw [suzukiDF6D4FixedGridShard290EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 591
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard290EvenDotSoundness i
          suzukiDF6D4FixedGridShard290EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 591) := by
    simpa [suzukiDF6D4FixedGridShard290EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard290EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 591) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard290EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 591) := by
    rw [suzukiDF6D4FixedGridShard290EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 591
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard290EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard290EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard290EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard290EvenDotSoundness i
            suzukiDF6D4FixedGridShard290EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard290EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard290OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard290OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 591) := by
  have h := suzukiDF6D4FixedGridShard290Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard290OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 591)) at h
  exact h

theorem suzukiDF6D4FixedGridShard290OddFull_eq_live :
    suzukiDF6D4FixedGridShard290OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 591) := by
  have h := suzukiDF6D4FixedGridShard290Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard290OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 591)) at h
  exact h

def suzukiDF6D4FixedGridShard290OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard290OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard290OddDotSoundness i.val
        suzukiDF6D4FixedGridShard290OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard290OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard290OddResidualData =
      suzukiDF6D4FixedGridShard290OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard290Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard290OddResidualData =
    suzukiDF6D4FixedGridShard290OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard290OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard290OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 591 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard290OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 591) := by
    rw [suzukiDF6D4FixedGridShard290OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 591
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard290OddDotSoundness i
          suzukiDF6D4FixedGridShard290OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 591) := by
    simpa [suzukiDF6D4FixedGridShard290OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard290OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 591) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard290OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 591) := by
    rw [suzukiDF6D4FixedGridShard290OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 591
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard290OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard290OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard290OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard290OddDotSoundness i
            suzukiDF6D4FixedGridShard290OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard290OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
