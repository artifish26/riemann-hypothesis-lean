import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard277Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard277Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard277EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard277OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard277EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard277EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 578) := by
  have h := suzukiDF6D4FixedGridShard277Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard277EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 578)) at h
  exact h

theorem suzukiDF6D4FixedGridShard277EvenFull_eq_live :
    suzukiDF6D4FixedGridShard277EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 578) := by
  have h := suzukiDF6D4FixedGridShard277Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard277EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 578)) at h
  exact h

def suzukiDF6D4FixedGridShard277EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard277EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard277EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard277EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard277EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard277EvenResidualData =
      suzukiDF6D4FixedGridShard277EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard277Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard277EvenResidualData =
    suzukiDF6D4FixedGridShard277EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard277EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard277EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 578 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard277EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 578) := by
    rw [suzukiDF6D4FixedGridShard277EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 578
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard277EvenDotSoundness i
          suzukiDF6D4FixedGridShard277EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 578) := by
    simpa [suzukiDF6D4FixedGridShard277EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard277EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 578) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard277EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 578) := by
    rw [suzukiDF6D4FixedGridShard277EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 578
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard277EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard277EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard277EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard277EvenDotSoundness i
            suzukiDF6D4FixedGridShard277EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard277EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard277OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard277OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 578) := by
  have h := suzukiDF6D4FixedGridShard277Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard277OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 578)) at h
  exact h

theorem suzukiDF6D4FixedGridShard277OddFull_eq_live :
    suzukiDF6D4FixedGridShard277OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 578) := by
  have h := suzukiDF6D4FixedGridShard277Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard277OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 578)) at h
  exact h

def suzukiDF6D4FixedGridShard277OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard277OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard277OddDotSoundness i.val
        suzukiDF6D4FixedGridShard277OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard277OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard277OddResidualData =
      suzukiDF6D4FixedGridShard277OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard277Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard277OddResidualData =
    suzukiDF6D4FixedGridShard277OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard277OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard277OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 578 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard277OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 578) := by
    rw [suzukiDF6D4FixedGridShard277OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 578
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard277OddDotSoundness i
          suzukiDF6D4FixedGridShard277OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 578) := by
    simpa [suzukiDF6D4FixedGridShard277OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard277OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 578) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard277OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 578) := by
    rw [suzukiDF6D4FixedGridShard277OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 578
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard277OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard277OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard277OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard277OddDotSoundness i
            suzukiDF6D4FixedGridShard277OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard277OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
