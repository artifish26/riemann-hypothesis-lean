import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard289Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard289Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard289EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard289OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard289EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard289EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 590) := by
  have h := suzukiDF6D4FixedGridShard289Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard289EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 590)) at h
  exact h

theorem suzukiDF6D4FixedGridShard289EvenFull_eq_live :
    suzukiDF6D4FixedGridShard289EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 590) := by
  have h := suzukiDF6D4FixedGridShard289Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard289EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 590)) at h
  exact h

def suzukiDF6D4FixedGridShard289EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard289EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard289EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard289EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard289EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard289EvenResidualData =
      suzukiDF6D4FixedGridShard289EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard289Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard289EvenResidualData =
    suzukiDF6D4FixedGridShard289EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard289EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard289EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 590 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard289EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 590) := by
    rw [suzukiDF6D4FixedGridShard289EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 590
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard289EvenDotSoundness i
          suzukiDF6D4FixedGridShard289EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 590) := by
    simpa [suzukiDF6D4FixedGridShard289EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard289EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 590) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard289EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 590) := by
    rw [suzukiDF6D4FixedGridShard289EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 590
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard289EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard289EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard289EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard289EvenDotSoundness i
            suzukiDF6D4FixedGridShard289EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard289EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard289OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard289OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 590) := by
  have h := suzukiDF6D4FixedGridShard289Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard289OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 590)) at h
  exact h

theorem suzukiDF6D4FixedGridShard289OddFull_eq_live :
    suzukiDF6D4FixedGridShard289OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 590) := by
  have h := suzukiDF6D4FixedGridShard289Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard289OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 590)) at h
  exact h

def suzukiDF6D4FixedGridShard289OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard289OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard289OddDotSoundness i.val
        suzukiDF6D4FixedGridShard289OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard289OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard289OddResidualData =
      suzukiDF6D4FixedGridShard289OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard289Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard289OddResidualData =
    suzukiDF6D4FixedGridShard289OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard289OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard289OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 590 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard289OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 590) := by
    rw [suzukiDF6D4FixedGridShard289OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 590
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard289OddDotSoundness i
          suzukiDF6D4FixedGridShard289OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 590) := by
    simpa [suzukiDF6D4FixedGridShard289OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard289OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 590) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard289OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 590) := by
    rw [suzukiDF6D4FixedGridShard289OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 590
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard289OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard289OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard289OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard289OddDotSoundness i
            suzukiDF6D4FixedGridShard289OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard289OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
