import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard261Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard261Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard261EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard261OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard261EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard261EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 562) := by
  have h := suzukiDF6D4FixedGridShard261Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard261EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 562)) at h
  exact h

theorem suzukiDF6D4FixedGridShard261EvenFull_eq_live :
    suzukiDF6D4FixedGridShard261EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 562) := by
  have h := suzukiDF6D4FixedGridShard261Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard261EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 562)) at h
  exact h

def suzukiDF6D4FixedGridShard261EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard261EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard261EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard261EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard261EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard261EvenResidualData =
      suzukiDF6D4FixedGridShard261EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard261Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard261EvenResidualData =
    suzukiDF6D4FixedGridShard261EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard261EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard261EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 562 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard261EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 562) := by
    rw [suzukiDF6D4FixedGridShard261EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 562
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard261EvenDotSoundness i
          suzukiDF6D4FixedGridShard261EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 562) := by
    simpa [suzukiDF6D4FixedGridShard261EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard261EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 562) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard261EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 562) := by
    rw [suzukiDF6D4FixedGridShard261EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 562
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard261EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard261EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard261EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard261EvenDotSoundness i
            suzukiDF6D4FixedGridShard261EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard261EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard261OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard261OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 562) := by
  have h := suzukiDF6D4FixedGridShard261Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard261OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 562)) at h
  exact h

theorem suzukiDF6D4FixedGridShard261OddFull_eq_live :
    suzukiDF6D4FixedGridShard261OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 562) := by
  have h := suzukiDF6D4FixedGridShard261Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard261OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 562)) at h
  exact h

def suzukiDF6D4FixedGridShard261OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard261OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard261OddDotSoundness i.val
        suzukiDF6D4FixedGridShard261OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard261OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard261OddResidualData =
      suzukiDF6D4FixedGridShard261OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard261Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard261OddResidualData =
    suzukiDF6D4FixedGridShard261OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard261OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard261OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 562 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard261OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 562) := by
    rw [suzukiDF6D4FixedGridShard261OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 562
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard261OddDotSoundness i
          suzukiDF6D4FixedGridShard261OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 562) := by
    simpa [suzukiDF6D4FixedGridShard261OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard261OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 562) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard261OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 562) := by
    rw [suzukiDF6D4FixedGridShard261OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 562
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard261OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard261OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard261OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard261OddDotSoundness i
            suzukiDF6D4FixedGridShard261OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard261OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
