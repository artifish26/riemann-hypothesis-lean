import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard276Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard276Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard276EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard276OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard276EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard276EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 577) := by
  have h := suzukiDF6D4FixedGridShard276Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard276EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 577)) at h
  exact h

theorem suzukiDF6D4FixedGridShard276EvenFull_eq_live :
    suzukiDF6D4FixedGridShard276EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 577) := by
  have h := suzukiDF6D4FixedGridShard276Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard276EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 577)) at h
  exact h

def suzukiDF6D4FixedGridShard276EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard276EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard276EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard276EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard276EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard276EvenResidualData =
      suzukiDF6D4FixedGridShard276EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard276Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard276EvenResidualData =
    suzukiDF6D4FixedGridShard276EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard276EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard276EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 577 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard276EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 577) := by
    rw [suzukiDF6D4FixedGridShard276EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 577
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard276EvenDotSoundness i
          suzukiDF6D4FixedGridShard276EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 577) := by
    simpa [suzukiDF6D4FixedGridShard276EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard276EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 577) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard276EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 577) := by
    rw [suzukiDF6D4FixedGridShard276EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 577
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard276EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard276EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard276EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard276EvenDotSoundness i
            suzukiDF6D4FixedGridShard276EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard276EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard276OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard276OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 577) := by
  have h := suzukiDF6D4FixedGridShard276Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard276OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 577)) at h
  exact h

theorem suzukiDF6D4FixedGridShard276OddFull_eq_live :
    suzukiDF6D4FixedGridShard276OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 577) := by
  have h := suzukiDF6D4FixedGridShard276Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard276OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 577)) at h
  exact h

def suzukiDF6D4FixedGridShard276OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard276OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard276OddDotSoundness i.val
        suzukiDF6D4FixedGridShard276OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard276OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard276OddResidualData =
      suzukiDF6D4FixedGridShard276OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard276Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard276OddResidualData =
    suzukiDF6D4FixedGridShard276OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard276OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard276OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 577 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard276OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 577) := by
    rw [suzukiDF6D4FixedGridShard276OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 577
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard276OddDotSoundness i
          suzukiDF6D4FixedGridShard276OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 577) := by
    simpa [suzukiDF6D4FixedGridShard276OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard276OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 577) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard276OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 577) := by
    rw [suzukiDF6D4FixedGridShard276OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 577
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard276OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard276OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard276OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard276OddDotSoundness i
            suzukiDF6D4FixedGridShard276OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard276OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
