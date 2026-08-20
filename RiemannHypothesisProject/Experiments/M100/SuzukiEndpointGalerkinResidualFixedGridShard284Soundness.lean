import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard284Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard284Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridShard284EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard284OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a
theorem suzukiDF6D4FixedGridShard284EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard284EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 585) := by
  have h := suzukiDF6D4FixedGridShard284Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard284EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 585)) at h
  exact h

theorem suzukiDF6D4FixedGridShard284EvenFull_eq_live :
    suzukiDF6D4FixedGridShard284EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 585) := by
  have h := suzukiDF6D4FixedGridShard284Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard284EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 585)) at h
  exact h

def suzukiDF6D4FixedGridShard284EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard284EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard284EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard284EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard284EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard284EvenResidualData =
      suzukiDF6D4FixedGridShard284EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard284Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard284EvenResidualData =
    suzukiDF6D4FixedGridShard284EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard284EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard284EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 585 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard284EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 585) := by
    rw [suzukiDF6D4FixedGridShard284EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 585
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard284EvenDotSoundness i
          suzukiDF6D4FixedGridShard284EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 585) := by
    simpa [suzukiDF6D4FixedGridShard284EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard284EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 585) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard284EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 585) := by
    rw [suzukiDF6D4FixedGridShard284EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 585
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard284EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard284EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard284EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard284EvenDotSoundness i
            suzukiDF6D4FixedGridShard284EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard284EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard284OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard284OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 585) := by
  have h := suzukiDF6D4FixedGridShard284Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard284OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 585)) at h
  exact h

theorem suzukiDF6D4FixedGridShard284OddFull_eq_live :
    suzukiDF6D4FixedGridShard284OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 585) := by
  have h := suzukiDF6D4FixedGridShard284Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard284OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 585)) at h
  exact h

def suzukiDF6D4FixedGridShard284OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard284OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard284OddDotSoundness i.val
        suzukiDF6D4FixedGridShard284OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard284OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard284OddResidualData =
      suzukiDF6D4FixedGridShard284OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard284Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard284OddResidualData =
    suzukiDF6D4FixedGridShard284OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard284OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard284OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 585 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard284OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 585) := by
    rw [suzukiDF6D4FixedGridShard284OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 585
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard284OddDotSoundness i
          suzukiDF6D4FixedGridShard284OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 585) := by
    simpa [suzukiDF6D4FixedGridShard284OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard284OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 585) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard284OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 585) := by
    rw [suzukiDF6D4FixedGridShard284OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 585
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard284OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard284OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard284OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard284OddDotSoundness i
            suzukiDF6D4FixedGridShard284OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard284OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
