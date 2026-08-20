import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard196Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard196Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard196EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard196EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 196 k) := by
  have h := suzukiDF6D4FixedGridShard196Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard196EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 196 k)) at h
  exact h

def suzukiDF6D4FixedGridShard196EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard196EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard196EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard196EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard196EvenComparisonData)

theorem suzukiDF6D4FixedGridShard196EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard196EvenSolveData =
      suzukiDF6D4FixedGridShard196EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard196Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard196EvenSolveData =
    suzukiDF6D4FixedGridShard196EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard196EvenCross_eq_live :
    suzukiDF6D4FixedGridShard196EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 196) := by
  have h := suzukiDF6D4FixedGridShard196Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard196EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 196)) at h
  exact h

theorem suzukiDF6D4FixedGridShard196EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard196EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 196 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 196 k) := by
    rw [suzukiDF6D4FixedGridShard196EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 196 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196EvenDotSoundness i
          suzukiDF6D4FixedGridShard196EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 196 k) := by
    simpa [suzukiDF6D4FixedGridShard196EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard196EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 196 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 196) := by
    rw [suzukiDF6D4FixedGridShard196EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 196)
  rw [suzukiDF6D4FixedGridShard196EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard196EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard196EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard196EvenDotSoundness i
            suzukiDF6D4FixedGridShard196EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard196EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard196OddComparison_eq_live :
    suzukiDF6D4FixedGridShard196OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 196 k) := by
  have h := suzukiDF6D4FixedGridShard196Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard196OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 196 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard196OddCross_eq_live :
    suzukiDF6D4FixedGridShard196OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 196) := by
  have h := suzukiDF6D4FixedGridShard196Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard196OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 196)) at h
  exact h

def suzukiDF6D4FixedGridShard196OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard196OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard196OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard196OddDotSoundness i.val
      suzukiDF6D4FixedGridShard196OddComparisonData)

theorem suzukiDF6D4FixedGridShard196OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard196OddSolveData =
      suzukiDF6D4FixedGridShard196OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard196Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard196OddSolveData =
    suzukiDF6D4FixedGridShard196OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard196OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard196OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 196 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 196 k) := by
    rw [suzukiDF6D4FixedGridShard196OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 196 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196OddDotSoundness i
          suzukiDF6D4FixedGridShard196OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 196 k) := by
    simpa [suzukiDF6D4FixedGridShard196OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard196OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 196 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 196) := by
    rw [suzukiDF6D4FixedGridShard196OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 196)
  rw [suzukiDF6D4FixedGridShard196OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard196OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard196OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard196OddDotSoundness i
            suzukiDF6D4FixedGridShard196OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard196OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard196EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard196EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 497) := by
  have h := suzukiDF6D4FixedGridShard196Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard196EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 497)) at h
  exact h

theorem suzukiDF6D4FixedGridShard196EvenFull_eq_live :
    suzukiDF6D4FixedGridShard196EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 497) := by
  have h := suzukiDF6D4FixedGridShard196Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard196EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 497)) at h
  exact h

def suzukiDF6D4FixedGridShard196EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard196EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard196EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard196EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard196EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard196EvenResidualData =
      suzukiDF6D4FixedGridShard196EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard196Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard196EvenResidualData =
    suzukiDF6D4FixedGridShard196EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard196EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard196EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 497 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 497) := by
    rw [suzukiDF6D4FixedGridShard196EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 497
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196EvenDotSoundness i
          suzukiDF6D4FixedGridShard196EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 497) := by
    simpa [suzukiDF6D4FixedGridShard196EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard196EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 497) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 497) := by
    rw [suzukiDF6D4FixedGridShard196EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 497
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard196EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard196EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard196EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard196EvenDotSoundness i
            suzukiDF6D4FixedGridShard196EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard196EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard196OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard196OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 497) := by
  have h := suzukiDF6D4FixedGridShard196Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard196OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 497)) at h
  exact h

theorem suzukiDF6D4FixedGridShard196OddFull_eq_live :
    suzukiDF6D4FixedGridShard196OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 497) := by
  have h := suzukiDF6D4FixedGridShard196Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard196OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 497)) at h
  exact h

def suzukiDF6D4FixedGridShard196OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard196OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard196OddDotSoundness i.val
        suzukiDF6D4FixedGridShard196OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard196OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard196OddResidualData =
      suzukiDF6D4FixedGridShard196OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard196Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard196OddResidualData =
    suzukiDF6D4FixedGridShard196OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard196OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard196OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 497 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 497) := by
    rw [suzukiDF6D4FixedGridShard196OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 497
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196OddDotSoundness i
          suzukiDF6D4FixedGridShard196OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 497) := by
    simpa [suzukiDF6D4FixedGridShard196OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard196OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 497) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard196OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 497) := by
    rw [suzukiDF6D4FixedGridShard196OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 497
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard196OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard196OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard196OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard196OddDotSoundness i
            suzukiDF6D4FixedGridShard196OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard196OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
