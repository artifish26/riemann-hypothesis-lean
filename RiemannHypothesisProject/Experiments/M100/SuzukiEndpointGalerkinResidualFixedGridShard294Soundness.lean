import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard294Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard294Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard294EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard294OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard294EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard294EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 595) := by
  have h := suzukiDF6D4FixedGridShard294Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard294EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 595)) at h
  exact h

theorem suzukiDF6D4FixedGridShard294EvenFull_eq_live :
    suzukiDF6D4FixedGridShard294EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 595) := by
  have h := suzukiDF6D4FixedGridShard294Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard294EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 595)) at h
  exact h

def suzukiDF6D4FixedGridShard294EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard294EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard294EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard294EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard294EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard294EvenResidualData =
      suzukiDF6D4FixedGridShard294EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard294Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard294EvenResidualData =
    suzukiDF6D4FixedGridShard294EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard294EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard294EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 595 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard294EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 595) := by
    rw [suzukiDF6D4FixedGridShard294EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 595
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard294EvenDotSoundness i
          suzukiDF6D4FixedGridShard294EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 595) := by
    simpa [suzukiDF6D4FixedGridShard294EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard294EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 595) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard294EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 595) := by
    rw [suzukiDF6D4FixedGridShard294EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 595
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard294EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard294EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard294EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard294EvenDotSoundness i
            suzukiDF6D4FixedGridShard294EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard294EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard294OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard294OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 595) := by
  have h := suzukiDF6D4FixedGridShard294Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard294OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 595)) at h
  exact h

theorem suzukiDF6D4FixedGridShard294OddFull_eq_live :
    suzukiDF6D4FixedGridShard294OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 595) := by
  have h := suzukiDF6D4FixedGridShard294Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard294OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 595)) at h
  exact h

def suzukiDF6D4FixedGridShard294OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard294OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard294OddDotSoundness i.val
        suzukiDF6D4FixedGridShard294OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard294OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard294OddResidualData =
      suzukiDF6D4FixedGridShard294OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard294Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard294OddResidualData =
    suzukiDF6D4FixedGridShard294OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard294OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard294OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 595 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard294OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 595) := by
    rw [suzukiDF6D4FixedGridShard294OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 595
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard294OddDotSoundness i
          suzukiDF6D4FixedGridShard294OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 595) := by
    simpa [suzukiDF6D4FixedGridShard294OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard294OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 595) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard294OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 595) := by
    rw [suzukiDF6D4FixedGridShard294OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 595
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard294OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard294OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard294OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard294OddDotSoundness i
            suzukiDF6D4FixedGridShard294OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard294OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
