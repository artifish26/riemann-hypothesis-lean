import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard259Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard259Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard259EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard259OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard259EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard259EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 560) := by
  have h := suzukiDF6D4FixedGridShard259Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard259EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 560)) at h
  exact h

theorem suzukiDF6D4FixedGridShard259EvenFull_eq_live :
    suzukiDF6D4FixedGridShard259EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 560) := by
  have h := suzukiDF6D4FixedGridShard259Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard259EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 560)) at h
  exact h

def suzukiDF6D4FixedGridShard259EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard259EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard259EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard259EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard259EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard259EvenResidualData =
      suzukiDF6D4FixedGridShard259EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard259Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard259EvenResidualData =
    suzukiDF6D4FixedGridShard259EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard259EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard259EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 560 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard259EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 560) := by
    rw [suzukiDF6D4FixedGridShard259EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 560
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard259EvenDotSoundness i
          suzukiDF6D4FixedGridShard259EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 560) := by
    simpa [suzukiDF6D4FixedGridShard259EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard259EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 560) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard259EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 560) := by
    rw [suzukiDF6D4FixedGridShard259EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 560
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard259EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard259EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard259EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard259EvenDotSoundness i
            suzukiDF6D4FixedGridShard259EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard259EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard259OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard259OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 560) := by
  have h := suzukiDF6D4FixedGridShard259Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard259OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 560)) at h
  exact h

theorem suzukiDF6D4FixedGridShard259OddFull_eq_live :
    suzukiDF6D4FixedGridShard259OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 560) := by
  have h := suzukiDF6D4FixedGridShard259Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard259OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 560)) at h
  exact h

def suzukiDF6D4FixedGridShard259OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard259OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard259OddDotSoundness i.val
        suzukiDF6D4FixedGridShard259OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard259OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard259OddResidualData =
      suzukiDF6D4FixedGridShard259OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard259Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard259OddResidualData =
    suzukiDF6D4FixedGridShard259OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard259OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard259OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 560 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard259OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 560) := by
    rw [suzukiDF6D4FixedGridShard259OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 560
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard259OddDotSoundness i
          suzukiDF6D4FixedGridShard259OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 560) := by
    simpa [suzukiDF6D4FixedGridShard259OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard259OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 560) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard259OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 560) := by
    rw [suzukiDF6D4FixedGridShard259OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 560
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard259OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard259OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard259OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard259OddDotSoundness i
            suzukiDF6D4FixedGridShard259OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard259OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
