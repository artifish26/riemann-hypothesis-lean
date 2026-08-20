import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard268Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard268Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard268EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard268OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard268EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard268EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 569) := by
  have h := suzukiDF6D4FixedGridShard268Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard268EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 569)) at h
  exact h

theorem suzukiDF6D4FixedGridShard268EvenFull_eq_live :
    suzukiDF6D4FixedGridShard268EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 569) := by
  have h := suzukiDF6D4FixedGridShard268Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard268EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 569)) at h
  exact h

def suzukiDF6D4FixedGridShard268EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard268EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard268EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard268EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard268EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard268EvenResidualData =
      suzukiDF6D4FixedGridShard268EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard268Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard268EvenResidualData =
    suzukiDF6D4FixedGridShard268EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard268EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard268EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 569 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard268EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 569) := by
    rw [suzukiDF6D4FixedGridShard268EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 569
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard268EvenDotSoundness i
          suzukiDF6D4FixedGridShard268EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 569) := by
    simpa [suzukiDF6D4FixedGridShard268EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard268EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 569) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard268EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 569) := by
    rw [suzukiDF6D4FixedGridShard268EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 569
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard268EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard268EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard268EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard268EvenDotSoundness i
            suzukiDF6D4FixedGridShard268EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard268EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard268OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard268OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 569) := by
  have h := suzukiDF6D4FixedGridShard268Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard268OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 569)) at h
  exact h

theorem suzukiDF6D4FixedGridShard268OddFull_eq_live :
    suzukiDF6D4FixedGridShard268OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 569) := by
  have h := suzukiDF6D4FixedGridShard268Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard268OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 569)) at h
  exact h

def suzukiDF6D4FixedGridShard268OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard268OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard268OddDotSoundness i.val
        suzukiDF6D4FixedGridShard268OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard268OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard268OddResidualData =
      suzukiDF6D4FixedGridShard268OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard268Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard268OddResidualData =
    suzukiDF6D4FixedGridShard268OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard268OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard268OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 569 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard268OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 569) := by
    rw [suzukiDF6D4FixedGridShard268OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 569
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard268OddDotSoundness i
          suzukiDF6D4FixedGridShard268OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 569) := by
    simpa [suzukiDF6D4FixedGridShard268OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard268OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 569) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard268OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 569) := by
    rw [suzukiDF6D4FixedGridShard268OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 569
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard268OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard268OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard268OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard268OddDotSoundness i
            suzukiDF6D4FixedGridShard268OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard268OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
