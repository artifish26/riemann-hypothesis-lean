import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard266Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard266Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard266EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard266OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard266EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard266EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 567) := by
  have h := suzukiDF6D4FixedGridShard266Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard266EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 567)) at h
  exact h

theorem suzukiDF6D4FixedGridShard266EvenFull_eq_live :
    suzukiDF6D4FixedGridShard266EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 567) := by
  have h := suzukiDF6D4FixedGridShard266Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard266EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 567)) at h
  exact h

def suzukiDF6D4FixedGridShard266EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard266EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard266EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard266EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard266EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard266EvenResidualData =
      suzukiDF6D4FixedGridShard266EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard266Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard266EvenResidualData =
    suzukiDF6D4FixedGridShard266EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard266EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard266EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 567 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard266EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 567) := by
    rw [suzukiDF6D4FixedGridShard266EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 567
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard266EvenDotSoundness i
          suzukiDF6D4FixedGridShard266EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 567) := by
    simpa [suzukiDF6D4FixedGridShard266EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard266EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 567) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard266EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 567) := by
    rw [suzukiDF6D4FixedGridShard266EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 567
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard266EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard266EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard266EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard266EvenDotSoundness i
            suzukiDF6D4FixedGridShard266EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard266EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard266OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard266OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 567) := by
  have h := suzukiDF6D4FixedGridShard266Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard266OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 567)) at h
  exact h

theorem suzukiDF6D4FixedGridShard266OddFull_eq_live :
    suzukiDF6D4FixedGridShard266OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 567) := by
  have h := suzukiDF6D4FixedGridShard266Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard266OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 567)) at h
  exact h

def suzukiDF6D4FixedGridShard266OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard266OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard266OddDotSoundness i.val
        suzukiDF6D4FixedGridShard266OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard266OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard266OddResidualData =
      suzukiDF6D4FixedGridShard266OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard266Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard266OddResidualData =
    suzukiDF6D4FixedGridShard266OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard266OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard266OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 567 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard266OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 567) := by
    rw [suzukiDF6D4FixedGridShard266OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 567
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard266OddDotSoundness i
          suzukiDF6D4FixedGridShard266OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 567) := by
    simpa [suzukiDF6D4FixedGridShard266OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard266OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 567) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard266OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 567) := by
    rw [suzukiDF6D4FixedGridShard266OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 567
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard266OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard266OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard266OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard266OddDotSoundness i
            suzukiDF6D4FixedGridShard266OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard266OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
