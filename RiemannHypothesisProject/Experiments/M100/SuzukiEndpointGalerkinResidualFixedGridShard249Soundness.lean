import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard249Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard249Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard249EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard249EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 249 k) := by
  have h := suzukiDF6D4FixedGridShard249Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard249EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 249 k)) at h
  exact h

def suzukiDF6D4FixedGridShard249EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard249EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard249EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard249EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard249EvenComparisonData)

theorem suzukiDF6D4FixedGridShard249EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard249EvenSolveData =
      suzukiDF6D4FixedGridShard249EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard249Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard249EvenSolveData =
    suzukiDF6D4FixedGridShard249EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard249EvenCross_eq_live :
    suzukiDF6D4FixedGridShard249EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 249) := by
  have h := suzukiDF6D4FixedGridShard249Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard249EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 249)) at h
  exact h

theorem suzukiDF6D4FixedGridShard249EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard249EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 249 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 249 k) := by
    rw [suzukiDF6D4FixedGridShard249EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 249 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249EvenDotSoundness i
          suzukiDF6D4FixedGridShard249EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 249 k) := by
    simpa [suzukiDF6D4FixedGridShard249EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard249EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 249 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 249) := by
    rw [suzukiDF6D4FixedGridShard249EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 249)
  rw [suzukiDF6D4FixedGridShard249EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard249EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard249EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard249EvenDotSoundness i
            suzukiDF6D4FixedGridShard249EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard249EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard249OddComparison_eq_live :
    suzukiDF6D4FixedGridShard249OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 249 k) := by
  have h := suzukiDF6D4FixedGridShard249Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard249OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 249 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard249OddCross_eq_live :
    suzukiDF6D4FixedGridShard249OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 249) := by
  have h := suzukiDF6D4FixedGridShard249Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard249OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 249)) at h
  exact h

def suzukiDF6D4FixedGridShard249OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard249OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard249OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard249OddDotSoundness i.val
      suzukiDF6D4FixedGridShard249OddComparisonData)

theorem suzukiDF6D4FixedGridShard249OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard249OddSolveData =
      suzukiDF6D4FixedGridShard249OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard249Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard249OddSolveData =
    suzukiDF6D4FixedGridShard249OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard249OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard249OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 249 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 249 k) := by
    rw [suzukiDF6D4FixedGridShard249OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 249 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249OddDotSoundness i
          suzukiDF6D4FixedGridShard249OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 249 k) := by
    simpa [suzukiDF6D4FixedGridShard249OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard249OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 249 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 249) := by
    rw [suzukiDF6D4FixedGridShard249OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 249)
  rw [suzukiDF6D4FixedGridShard249OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard249OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard249OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard249OddDotSoundness i
            suzukiDF6D4FixedGridShard249OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard249OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard249EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard249EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 550) := by
  have h := suzukiDF6D4FixedGridShard249Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard249EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 550)) at h
  exact h

theorem suzukiDF6D4FixedGridShard249EvenFull_eq_live :
    suzukiDF6D4FixedGridShard249EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 550) := by
  have h := suzukiDF6D4FixedGridShard249Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard249EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 550)) at h
  exact h

def suzukiDF6D4FixedGridShard249EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard249EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard249EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard249EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard249EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard249EvenResidualData =
      suzukiDF6D4FixedGridShard249EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard249Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard249EvenResidualData =
    suzukiDF6D4FixedGridShard249EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard249EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard249EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 550 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 550) := by
    rw [suzukiDF6D4FixedGridShard249EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 550
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249EvenDotSoundness i
          suzukiDF6D4FixedGridShard249EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 550) := by
    simpa [suzukiDF6D4FixedGridShard249EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard249EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 550) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 550) := by
    rw [suzukiDF6D4FixedGridShard249EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 550
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard249EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard249EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard249EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard249EvenDotSoundness i
            suzukiDF6D4FixedGridShard249EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard249EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard249OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard249OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 550) := by
  have h := suzukiDF6D4FixedGridShard249Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard249OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 550)) at h
  exact h

theorem suzukiDF6D4FixedGridShard249OddFull_eq_live :
    suzukiDF6D4FixedGridShard249OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 550) := by
  have h := suzukiDF6D4FixedGridShard249Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard249OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 550)) at h
  exact h

def suzukiDF6D4FixedGridShard249OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard249OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard249OddDotSoundness i.val
        suzukiDF6D4FixedGridShard249OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard249OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard249OddResidualData =
      suzukiDF6D4FixedGridShard249OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard249Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard249OddResidualData =
    suzukiDF6D4FixedGridShard249OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard249OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard249OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 550 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 550) := by
    rw [suzukiDF6D4FixedGridShard249OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 550
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249OddDotSoundness i
          suzukiDF6D4FixedGridShard249OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 550) := by
    simpa [suzukiDF6D4FixedGridShard249OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard249OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 550) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard249OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 550) := by
    rw [suzukiDF6D4FixedGridShard249OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 550
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard249OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard249OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard249OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard249OddDotSoundness i
            suzukiDF6D4FixedGridShard249OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard249OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
