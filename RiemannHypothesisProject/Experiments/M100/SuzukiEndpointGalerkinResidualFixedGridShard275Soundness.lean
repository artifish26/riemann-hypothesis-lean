import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard275Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard275Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard275EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard275OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard275EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard275EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 576) := by
  have h := suzukiDF6D4FixedGridShard275Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard275EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 576)) at h
  exact h

theorem suzukiDF6D4FixedGridShard275EvenFull_eq_live :
    suzukiDF6D4FixedGridShard275EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 576) := by
  have h := suzukiDF6D4FixedGridShard275Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard275EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 576)) at h
  exact h

def suzukiDF6D4FixedGridShard275EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard275EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard275EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard275EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard275EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard275EvenResidualData =
      suzukiDF6D4FixedGridShard275EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard275Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard275EvenResidualData =
    suzukiDF6D4FixedGridShard275EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard275EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard275EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 576 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard275EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 576) := by
    rw [suzukiDF6D4FixedGridShard275EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 576
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard275EvenDotSoundness i
          suzukiDF6D4FixedGridShard275EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 576) := by
    simpa [suzukiDF6D4FixedGridShard275EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard275EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 576) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard275EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 576) := by
    rw [suzukiDF6D4FixedGridShard275EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 576
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard275EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard275EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard275EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard275EvenDotSoundness i
            suzukiDF6D4FixedGridShard275EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard275EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard275OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard275OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 576) := by
  have h := suzukiDF6D4FixedGridShard275Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard275OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 576)) at h
  exact h

theorem suzukiDF6D4FixedGridShard275OddFull_eq_live :
    suzukiDF6D4FixedGridShard275OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 576) := by
  have h := suzukiDF6D4FixedGridShard275Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard275OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 576)) at h
  exact h

def suzukiDF6D4FixedGridShard275OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard275OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard275OddDotSoundness i.val
        suzukiDF6D4FixedGridShard275OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard275OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard275OddResidualData =
      suzukiDF6D4FixedGridShard275OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard275Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard275OddResidualData =
    suzukiDF6D4FixedGridShard275OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard275OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard275OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 576 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard275OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 576) := by
    rw [suzukiDF6D4FixedGridShard275OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 576
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard275OddDotSoundness i
          suzukiDF6D4FixedGridShard275OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 576) := by
    simpa [suzukiDF6D4FixedGridShard275OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard275OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 576) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard275OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 576) := by
    rw [suzukiDF6D4FixedGridShard275OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 576
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard275OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard275OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard275OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard275OddDotSoundness i
            suzukiDF6D4FixedGridShard275OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard275OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
