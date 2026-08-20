import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard297Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard297Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard297EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard297OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard297EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard297EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 598) := by
  have h := suzukiDF6D4FixedGridShard297Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard297EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 598)) at h
  exact h

theorem suzukiDF6D4FixedGridShard297EvenFull_eq_live :
    suzukiDF6D4FixedGridShard297EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 598) := by
  have h := suzukiDF6D4FixedGridShard297Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard297EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 598)) at h
  exact h

def suzukiDF6D4FixedGridShard297EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard297EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard297EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard297EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard297EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard297EvenResidualData =
      suzukiDF6D4FixedGridShard297EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard297Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard297EvenResidualData =
    suzukiDF6D4FixedGridShard297EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard297EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard297EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 598 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard297EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 598) := by
    rw [suzukiDF6D4FixedGridShard297EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 598
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard297EvenDotSoundness i
          suzukiDF6D4FixedGridShard297EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 598) := by
    simpa [suzukiDF6D4FixedGridShard297EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard297EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 598) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard297EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 598) := by
    rw [suzukiDF6D4FixedGridShard297EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 598
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard297EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard297EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard297EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard297EvenDotSoundness i
            suzukiDF6D4FixedGridShard297EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard297EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard297OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard297OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 598) := by
  have h := suzukiDF6D4FixedGridShard297Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard297OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 598)) at h
  exact h

theorem suzukiDF6D4FixedGridShard297OddFull_eq_live :
    suzukiDF6D4FixedGridShard297OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 598) := by
  have h := suzukiDF6D4FixedGridShard297Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard297OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 598)) at h
  exact h

def suzukiDF6D4FixedGridShard297OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard297OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard297OddDotSoundness i.val
        suzukiDF6D4FixedGridShard297OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard297OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard297OddResidualData =
      suzukiDF6D4FixedGridShard297OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard297Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard297OddResidualData =
    suzukiDF6D4FixedGridShard297OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard297OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard297OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 598 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard297OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 598) := by
    rw [suzukiDF6D4FixedGridShard297OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 598
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard297OddDotSoundness i
          suzukiDF6D4FixedGridShard297OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 598) := by
    simpa [suzukiDF6D4FixedGridShard297OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard297OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 598) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard297OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 598) := by
    rw [suzukiDF6D4FixedGridShard297OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 598
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard297OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard297OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard297OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard297OddDotSoundness i
            suzukiDF6D4FixedGridShard297OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard297OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
