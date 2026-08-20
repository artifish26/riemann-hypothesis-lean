import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard101Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard101Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard101EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard101EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 101 k) := by
  have h := suzukiDF6D4FixedGridShard101Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard101EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 101 k)) at h
  exact h

def suzukiDF6D4FixedGridShard101EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard101EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard101EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard101EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard101EvenComparisonData)

theorem suzukiDF6D4FixedGridShard101EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard101EvenSolveData =
      suzukiDF6D4FixedGridShard101EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard101Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard101EvenSolveData =
    suzukiDF6D4FixedGridShard101EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard101EvenCross_eq_live :
    suzukiDF6D4FixedGridShard101EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 101) := by
  have h := suzukiDF6D4FixedGridShard101Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard101EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 101)) at h
  exact h

theorem suzukiDF6D4FixedGridShard101EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard101EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 101 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 101 k) := by
    rw [suzukiDF6D4FixedGridShard101EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 101 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101EvenDotSoundness i
          suzukiDF6D4FixedGridShard101EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 101 k) := by
    simpa [suzukiDF6D4FixedGridShard101EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard101EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 101 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 101) := by
    rw [suzukiDF6D4FixedGridShard101EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 101)
  rw [suzukiDF6D4FixedGridShard101EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard101EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard101EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard101EvenDotSoundness i
            suzukiDF6D4FixedGridShard101EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard101EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard101OddComparison_eq_live :
    suzukiDF6D4FixedGridShard101OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 101 k) := by
  have h := suzukiDF6D4FixedGridShard101Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard101OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 101 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard101OddCross_eq_live :
    suzukiDF6D4FixedGridShard101OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 101) := by
  have h := suzukiDF6D4FixedGridShard101Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard101OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 101)) at h
  exact h

def suzukiDF6D4FixedGridShard101OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard101OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard101OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard101OddDotSoundness i.val
      suzukiDF6D4FixedGridShard101OddComparisonData)

theorem suzukiDF6D4FixedGridShard101OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard101OddSolveData =
      suzukiDF6D4FixedGridShard101OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard101Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard101OddSolveData =
    suzukiDF6D4FixedGridShard101OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard101OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard101OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 101 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 101 k) := by
    rw [suzukiDF6D4FixedGridShard101OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 101 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101OddDotSoundness i
          suzukiDF6D4FixedGridShard101OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 101 k) := by
    simpa [suzukiDF6D4FixedGridShard101OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard101OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 101 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 101) := by
    rw [suzukiDF6D4FixedGridShard101OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 101)
  rw [suzukiDF6D4FixedGridShard101OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard101OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard101OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard101OddDotSoundness i
            suzukiDF6D4FixedGridShard101OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard101OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard101EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard101EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 402) := by
  have h := suzukiDF6D4FixedGridShard101Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard101EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 402)) at h
  exact h

theorem suzukiDF6D4FixedGridShard101EvenFull_eq_live :
    suzukiDF6D4FixedGridShard101EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 402) := by
  have h := suzukiDF6D4FixedGridShard101Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard101EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 402)) at h
  exact h

def suzukiDF6D4FixedGridShard101EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard101EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard101EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard101EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard101EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard101EvenResidualData =
      suzukiDF6D4FixedGridShard101EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard101Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard101EvenResidualData =
    suzukiDF6D4FixedGridShard101EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard101EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard101EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 402 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 402) := by
    rw [suzukiDF6D4FixedGridShard101EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 402
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101EvenDotSoundness i
          suzukiDF6D4FixedGridShard101EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 402) := by
    simpa [suzukiDF6D4FixedGridShard101EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard101EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 402) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 402) := by
    rw [suzukiDF6D4FixedGridShard101EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 402
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard101EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard101EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard101EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard101EvenDotSoundness i
            suzukiDF6D4FixedGridShard101EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard101EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard101OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard101OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 402) := by
  have h := suzukiDF6D4FixedGridShard101Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard101OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 402)) at h
  exact h

theorem suzukiDF6D4FixedGridShard101OddFull_eq_live :
    suzukiDF6D4FixedGridShard101OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 402) := by
  have h := suzukiDF6D4FixedGridShard101Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard101OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 402)) at h
  exact h

def suzukiDF6D4FixedGridShard101OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard101OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard101OddDotSoundness i.val
        suzukiDF6D4FixedGridShard101OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard101OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard101OddResidualData =
      suzukiDF6D4FixedGridShard101OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard101Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard101OddResidualData =
    suzukiDF6D4FixedGridShard101OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard101OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard101OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 402 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 402) := by
    rw [suzukiDF6D4FixedGridShard101OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 402
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101OddDotSoundness i
          suzukiDF6D4FixedGridShard101OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 402) := by
    simpa [suzukiDF6D4FixedGridShard101OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard101OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 402) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard101OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 402) := by
    rw [suzukiDF6D4FixedGridShard101OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 402
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard101OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard101OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard101OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard101OddDotSoundness i
            suzukiDF6D4FixedGridShard101OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard101OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
