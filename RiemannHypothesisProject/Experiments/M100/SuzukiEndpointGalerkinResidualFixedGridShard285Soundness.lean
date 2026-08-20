import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard285Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard285Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard285EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard285OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard285EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard285EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 586) := by
  have h := suzukiDF6D4FixedGridShard285Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard285EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 586)) at h
  exact h

theorem suzukiDF6D4FixedGridShard285EvenFull_eq_live :
    suzukiDF6D4FixedGridShard285EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 586) := by
  have h := suzukiDF6D4FixedGridShard285Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard285EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 586)) at h
  exact h

def suzukiDF6D4FixedGridShard285EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard285EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard285EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard285EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard285EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard285EvenResidualData =
      suzukiDF6D4FixedGridShard285EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard285Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard285EvenResidualData =
    suzukiDF6D4FixedGridShard285EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard285EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard285EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 586 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard285EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 586) := by
    rw [suzukiDF6D4FixedGridShard285EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 586
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard285EvenDotSoundness i
          suzukiDF6D4FixedGridShard285EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 586) := by
    simpa [suzukiDF6D4FixedGridShard285EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard285EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 586) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard285EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 586) := by
    rw [suzukiDF6D4FixedGridShard285EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 586
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard285EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard285EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard285EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard285EvenDotSoundness i
            suzukiDF6D4FixedGridShard285EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard285EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard285OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard285OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 586) := by
  have h := suzukiDF6D4FixedGridShard285Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard285OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 586)) at h
  exact h

theorem suzukiDF6D4FixedGridShard285OddFull_eq_live :
    suzukiDF6D4FixedGridShard285OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 586) := by
  have h := suzukiDF6D4FixedGridShard285Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard285OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 586)) at h
  exact h

def suzukiDF6D4FixedGridShard285OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard285OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard285OddDotSoundness i.val
        suzukiDF6D4FixedGridShard285OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard285OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard285OddResidualData =
      suzukiDF6D4FixedGridShard285OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard285Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard285OddResidualData =
    suzukiDF6D4FixedGridShard285OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard285OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard285OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 586 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard285OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 586) := by
    rw [suzukiDF6D4FixedGridShard285OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 586
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard285OddDotSoundness i
          suzukiDF6D4FixedGridShard285OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 586) := by
    simpa [suzukiDF6D4FixedGridShard285OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard285OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 586) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard285OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 586) := by
    rw [suzukiDF6D4FixedGridShard285OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 586
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard285OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard285OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard285OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard285OddDotSoundness i
            suzukiDF6D4FixedGridShard285OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard285OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
