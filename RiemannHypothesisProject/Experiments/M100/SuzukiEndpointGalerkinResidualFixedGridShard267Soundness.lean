import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard267Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard267Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard267EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard267OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard267EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard267EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 568) := by
  have h := suzukiDF6D4FixedGridShard267Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard267EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 568)) at h
  exact h

theorem suzukiDF6D4FixedGridShard267EvenFull_eq_live :
    suzukiDF6D4FixedGridShard267EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 568) := by
  have h := suzukiDF6D4FixedGridShard267Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard267EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 568)) at h
  exact h

def suzukiDF6D4FixedGridShard267EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard267EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard267EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard267EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard267EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard267EvenResidualData =
      suzukiDF6D4FixedGridShard267EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard267Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard267EvenResidualData =
    suzukiDF6D4FixedGridShard267EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard267EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard267EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 568 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard267EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 568) := by
    rw [suzukiDF6D4FixedGridShard267EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 568
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard267EvenDotSoundness i
          suzukiDF6D4FixedGridShard267EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 568) := by
    simpa [suzukiDF6D4FixedGridShard267EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard267EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 568) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard267EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 568) := by
    rw [suzukiDF6D4FixedGridShard267EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 568
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard267EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard267EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard267EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard267EvenDotSoundness i
            suzukiDF6D4FixedGridShard267EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard267EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard267OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard267OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 568) := by
  have h := suzukiDF6D4FixedGridShard267Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard267OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 568)) at h
  exact h

theorem suzukiDF6D4FixedGridShard267OddFull_eq_live :
    suzukiDF6D4FixedGridShard267OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 568) := by
  have h := suzukiDF6D4FixedGridShard267Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard267OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 568)) at h
  exact h

def suzukiDF6D4FixedGridShard267OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard267OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard267OddDotSoundness i.val
        suzukiDF6D4FixedGridShard267OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard267OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard267OddResidualData =
      suzukiDF6D4FixedGridShard267OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard267Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard267OddResidualData =
    suzukiDF6D4FixedGridShard267OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard267OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard267OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 568 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard267OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 568) := by
    rw [suzukiDF6D4FixedGridShard267OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 568
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard267OddDotSoundness i
          suzukiDF6D4FixedGridShard267OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 568) := by
    simpa [suzukiDF6D4FixedGridShard267OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard267OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 568) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard267OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 568) := by
    rw [suzukiDF6D4FixedGridShard267OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 568
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard267OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard267OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard267OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard267OddDotSoundness i
            suzukiDF6D4FixedGridShard267OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard267OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
