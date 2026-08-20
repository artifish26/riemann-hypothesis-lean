import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard257Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard257Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard257EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard257OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard257EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard257EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 558) := by
  have h := suzukiDF6D4FixedGridShard257Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard257EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 558)) at h
  exact h

theorem suzukiDF6D4FixedGridShard257EvenFull_eq_live :
    suzukiDF6D4FixedGridShard257EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 558) := by
  have h := suzukiDF6D4FixedGridShard257Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard257EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 558)) at h
  exact h

def suzukiDF6D4FixedGridShard257EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard257EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard257EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard257EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard257EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard257EvenResidualData =
      suzukiDF6D4FixedGridShard257EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard257Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard257EvenResidualData =
    suzukiDF6D4FixedGridShard257EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard257EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard257EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 558 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard257EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 558) := by
    rw [suzukiDF6D4FixedGridShard257EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 558
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard257EvenDotSoundness i
          suzukiDF6D4FixedGridShard257EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 558) := by
    simpa [suzukiDF6D4FixedGridShard257EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard257EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 558) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard257EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 558) := by
    rw [suzukiDF6D4FixedGridShard257EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 558
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard257EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard257EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard257EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard257EvenDotSoundness i
            suzukiDF6D4FixedGridShard257EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard257EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard257OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard257OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 558) := by
  have h := suzukiDF6D4FixedGridShard257Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard257OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 558)) at h
  exact h

theorem suzukiDF6D4FixedGridShard257OddFull_eq_live :
    suzukiDF6D4FixedGridShard257OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 558) := by
  have h := suzukiDF6D4FixedGridShard257Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard257OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 558)) at h
  exact h

def suzukiDF6D4FixedGridShard257OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard257OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard257OddDotSoundness i.val
        suzukiDF6D4FixedGridShard257OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard257OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard257OddResidualData =
      suzukiDF6D4FixedGridShard257OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard257Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard257OddResidualData =
    suzukiDF6D4FixedGridShard257OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard257OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard257OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 558 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard257OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 558) := by
    rw [suzukiDF6D4FixedGridShard257OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 558
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard257OddDotSoundness i
          suzukiDF6D4FixedGridShard257OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 558) := by
    simpa [suzukiDF6D4FixedGridShard257OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard257OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 558) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard257OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 558) := by
    rw [suzukiDF6D4FixedGridShard257OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 558
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard257OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard257OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard257OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard257OddDotSoundness i
            suzukiDF6D4FixedGridShard257OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard257OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
