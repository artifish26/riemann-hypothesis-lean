import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard281Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard281Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard281EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard281OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard281EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard281EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 582) := by
  have h := suzukiDF6D4FixedGridShard281Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard281EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 582)) at h
  exact h

theorem suzukiDF6D4FixedGridShard281EvenFull_eq_live :
    suzukiDF6D4FixedGridShard281EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 582) := by
  have h := suzukiDF6D4FixedGridShard281Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard281EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 582)) at h
  exact h

def suzukiDF6D4FixedGridShard281EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard281EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard281EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard281EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard281EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard281EvenResidualData =
      suzukiDF6D4FixedGridShard281EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard281Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard281EvenResidualData =
    suzukiDF6D4FixedGridShard281EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard281EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard281EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 582 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard281EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 582) := by
    rw [suzukiDF6D4FixedGridShard281EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 582
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard281EvenDotSoundness i
          suzukiDF6D4FixedGridShard281EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 582) := by
    simpa [suzukiDF6D4FixedGridShard281EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard281EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 582) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard281EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 582) := by
    rw [suzukiDF6D4FixedGridShard281EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 582
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard281EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard281EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard281EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard281EvenDotSoundness i
            suzukiDF6D4FixedGridShard281EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard281EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard281OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard281OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 582) := by
  have h := suzukiDF6D4FixedGridShard281Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard281OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 582)) at h
  exact h

theorem suzukiDF6D4FixedGridShard281OddFull_eq_live :
    suzukiDF6D4FixedGridShard281OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 582) := by
  have h := suzukiDF6D4FixedGridShard281Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard281OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 582)) at h
  exact h

def suzukiDF6D4FixedGridShard281OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard281OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard281OddDotSoundness i.val
        suzukiDF6D4FixedGridShard281OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard281OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard281OddResidualData =
      suzukiDF6D4FixedGridShard281OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard281Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard281OddResidualData =
    suzukiDF6D4FixedGridShard281OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard281OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard281OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 582 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard281OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 582) := by
    rw [suzukiDF6D4FixedGridShard281OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 582
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard281OddDotSoundness i
          suzukiDF6D4FixedGridShard281OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 582) := by
    simpa [suzukiDF6D4FixedGridShard281OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard281OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 582) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard281OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 582) := by
    rw [suzukiDF6D4FixedGridShard281OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 582
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard281OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard281OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard281OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard281OddDotSoundness i
            suzukiDF6D4FixedGridShard281OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard281OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
