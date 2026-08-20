import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard287Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard287Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard287EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard287OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard287EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard287EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 588) := by
  have h := suzukiDF6D4FixedGridShard287Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard287EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 588)) at h
  exact h

theorem suzukiDF6D4FixedGridShard287EvenFull_eq_live :
    suzukiDF6D4FixedGridShard287EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 588) := by
  have h := suzukiDF6D4FixedGridShard287Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard287EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 588)) at h
  exact h

def suzukiDF6D4FixedGridShard287EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard287EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard287EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard287EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard287EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard287EvenResidualData =
      suzukiDF6D4FixedGridShard287EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard287Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard287EvenResidualData =
    suzukiDF6D4FixedGridShard287EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard287EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard287EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 588 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard287EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 588) := by
    rw [suzukiDF6D4FixedGridShard287EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 588
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard287EvenDotSoundness i
          suzukiDF6D4FixedGridShard287EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 588) := by
    simpa [suzukiDF6D4FixedGridShard287EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard287EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 588) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard287EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 588) := by
    rw [suzukiDF6D4FixedGridShard287EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 588
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard287EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard287EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard287EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard287EvenDotSoundness i
            suzukiDF6D4FixedGridShard287EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard287EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard287OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard287OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 588) := by
  have h := suzukiDF6D4FixedGridShard287Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard287OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 588)) at h
  exact h

theorem suzukiDF6D4FixedGridShard287OddFull_eq_live :
    suzukiDF6D4FixedGridShard287OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 588) := by
  have h := suzukiDF6D4FixedGridShard287Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard287OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 588)) at h
  exact h

def suzukiDF6D4FixedGridShard287OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard287OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard287OddDotSoundness i.val
        suzukiDF6D4FixedGridShard287OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard287OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard287OddResidualData =
      suzukiDF6D4FixedGridShard287OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard287Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard287OddResidualData =
    suzukiDF6D4FixedGridShard287OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard287OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard287OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 588 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard287OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 588) := by
    rw [suzukiDF6D4FixedGridShard287OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 588
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard287OddDotSoundness i
          suzukiDF6D4FixedGridShard287OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 588) := by
    simpa [suzukiDF6D4FixedGridShard287OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard287OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 588) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard287OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 588) := by
    rw [suzukiDF6D4FixedGridShard287OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 588
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard287OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard287OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard287OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard287OddDotSoundness i
            suzukiDF6D4FixedGridShard287OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard287OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
