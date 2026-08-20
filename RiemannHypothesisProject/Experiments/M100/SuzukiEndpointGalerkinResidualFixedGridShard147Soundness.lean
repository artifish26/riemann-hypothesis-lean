import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard147Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard147Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard147EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard147EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 147 k) := by
  have h := suzukiDF6D4FixedGridShard147Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard147EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 147 k)) at h
  exact h

def suzukiDF6D4FixedGridShard147EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard147EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard147EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard147EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard147EvenComparisonData)

theorem suzukiDF6D4FixedGridShard147EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard147EvenSolveData =
      suzukiDF6D4FixedGridShard147EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard147Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard147EvenSolveData =
    suzukiDF6D4FixedGridShard147EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard147EvenCross_eq_live :
    suzukiDF6D4FixedGridShard147EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 147) := by
  have h := suzukiDF6D4FixedGridShard147Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard147EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 147)) at h
  exact h

theorem suzukiDF6D4FixedGridShard147EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard147EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 147 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 147 k) := by
    rw [suzukiDF6D4FixedGridShard147EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 147 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147EvenDotSoundness i
          suzukiDF6D4FixedGridShard147EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 147 k) := by
    simpa [suzukiDF6D4FixedGridShard147EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard147EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 147 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 147) := by
    rw [suzukiDF6D4FixedGridShard147EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 147)
  rw [suzukiDF6D4FixedGridShard147EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard147EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard147EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard147EvenDotSoundness i
            suzukiDF6D4FixedGridShard147EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard147EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard147OddComparison_eq_live :
    suzukiDF6D4FixedGridShard147OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 147 k) := by
  have h := suzukiDF6D4FixedGridShard147Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard147OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 147 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard147OddCross_eq_live :
    suzukiDF6D4FixedGridShard147OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 147) := by
  have h := suzukiDF6D4FixedGridShard147Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard147OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 147)) at h
  exact h

def suzukiDF6D4FixedGridShard147OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard147OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard147OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard147OddDotSoundness i.val
      suzukiDF6D4FixedGridShard147OddComparisonData)

theorem suzukiDF6D4FixedGridShard147OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard147OddSolveData =
      suzukiDF6D4FixedGridShard147OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard147Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard147OddSolveData =
    suzukiDF6D4FixedGridShard147OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard147OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard147OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 147 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 147 k) := by
    rw [suzukiDF6D4FixedGridShard147OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 147 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147OddDotSoundness i
          suzukiDF6D4FixedGridShard147OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 147 k) := by
    simpa [suzukiDF6D4FixedGridShard147OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard147OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 147 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 147) := by
    rw [suzukiDF6D4FixedGridShard147OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 147)
  rw [suzukiDF6D4FixedGridShard147OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard147OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard147OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard147OddDotSoundness i
            suzukiDF6D4FixedGridShard147OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard147OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard147EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard147EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 448) := by
  have h := suzukiDF6D4FixedGridShard147Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard147EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 448)) at h
  exact h

theorem suzukiDF6D4FixedGridShard147EvenFull_eq_live :
    suzukiDF6D4FixedGridShard147EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 448) := by
  have h := suzukiDF6D4FixedGridShard147Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard147EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 448)) at h
  exact h

def suzukiDF6D4FixedGridShard147EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard147EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard147EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard147EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard147EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard147EvenResidualData =
      suzukiDF6D4FixedGridShard147EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard147Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard147EvenResidualData =
    suzukiDF6D4FixedGridShard147EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard147EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard147EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 448 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 448) := by
    rw [suzukiDF6D4FixedGridShard147EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 448
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147EvenDotSoundness i
          suzukiDF6D4FixedGridShard147EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 448) := by
    simpa [suzukiDF6D4FixedGridShard147EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard147EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 448) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 448) := by
    rw [suzukiDF6D4FixedGridShard147EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 448
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard147EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard147EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard147EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard147EvenDotSoundness i
            suzukiDF6D4FixedGridShard147EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard147EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard147OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard147OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 448) := by
  have h := suzukiDF6D4FixedGridShard147Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard147OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 448)) at h
  exact h

theorem suzukiDF6D4FixedGridShard147OddFull_eq_live :
    suzukiDF6D4FixedGridShard147OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 448) := by
  have h := suzukiDF6D4FixedGridShard147Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard147OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 448)) at h
  exact h

def suzukiDF6D4FixedGridShard147OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard147OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard147OddDotSoundness i.val
        suzukiDF6D4FixedGridShard147OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard147OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard147OddResidualData =
      suzukiDF6D4FixedGridShard147OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard147Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard147OddResidualData =
    suzukiDF6D4FixedGridShard147OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard147OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard147OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 448 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 448) := by
    rw [suzukiDF6D4FixedGridShard147OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 448
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147OddDotSoundness i
          suzukiDF6D4FixedGridShard147OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 448) := by
    simpa [suzukiDF6D4FixedGridShard147OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard147OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 448) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard147OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 448) := by
    rw [suzukiDF6D4FixedGridShard147OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 448
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard147OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard147OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard147OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard147OddDotSoundness i
            suzukiDF6D4FixedGridShard147OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard147OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
