import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard258Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard258Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard258EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard258OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard258EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard258EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 559) := by
  have h := suzukiDF6D4FixedGridShard258Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard258EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 559)) at h
  exact h

theorem suzukiDF6D4FixedGridShard258EvenFull_eq_live :
    suzukiDF6D4FixedGridShard258EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 559) := by
  have h := suzukiDF6D4FixedGridShard258Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard258EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 559)) at h
  exact h

def suzukiDF6D4FixedGridShard258EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard258EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard258EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard258EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard258EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard258EvenResidualData =
      suzukiDF6D4FixedGridShard258EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard258Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard258EvenResidualData =
    suzukiDF6D4FixedGridShard258EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard258EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard258EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 559 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard258EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 559) := by
    rw [suzukiDF6D4FixedGridShard258EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 559
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard258EvenDotSoundness i
          suzukiDF6D4FixedGridShard258EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 559) := by
    simpa [suzukiDF6D4FixedGridShard258EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard258EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 559) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard258EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 559) := by
    rw [suzukiDF6D4FixedGridShard258EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 559
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard258EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard258EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard258EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard258EvenDotSoundness i
            suzukiDF6D4FixedGridShard258EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard258EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard258OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard258OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 559) := by
  have h := suzukiDF6D4FixedGridShard258Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard258OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 559)) at h
  exact h

theorem suzukiDF6D4FixedGridShard258OddFull_eq_live :
    suzukiDF6D4FixedGridShard258OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 559) := by
  have h := suzukiDF6D4FixedGridShard258Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard258OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 559)) at h
  exact h

def suzukiDF6D4FixedGridShard258OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard258OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard258OddDotSoundness i.val
        suzukiDF6D4FixedGridShard258OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard258OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard258OddResidualData =
      suzukiDF6D4FixedGridShard258OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard258Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard258OddResidualData =
    suzukiDF6D4FixedGridShard258OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard258OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard258OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 559 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard258OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 559) := by
    rw [suzukiDF6D4FixedGridShard258OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 559
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard258OddDotSoundness i
          suzukiDF6D4FixedGridShard258OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 559) := by
    simpa [suzukiDF6D4FixedGridShard258OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard258OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 559) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard258OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 559) := by
    rw [suzukiDF6D4FixedGridShard258OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 559
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard258OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard258OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard258OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard258OddDotSoundness i
            suzukiDF6D4FixedGridShard258OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard258OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
