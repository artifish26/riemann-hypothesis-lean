import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard120Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard120Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard120EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard120EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 120 k) := by
  have h := suzukiDF6D4FixedGridShard120Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard120EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 120 k)) at h
  exact h

def suzukiDF6D4FixedGridShard120EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard120EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard120EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard120EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard120EvenComparisonData)

theorem suzukiDF6D4FixedGridShard120EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard120EvenSolveData =
      suzukiDF6D4FixedGridShard120EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard120Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard120EvenSolveData =
    suzukiDF6D4FixedGridShard120EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard120EvenCross_eq_live :
    suzukiDF6D4FixedGridShard120EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 120) := by
  have h := suzukiDF6D4FixedGridShard120Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard120EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 120)) at h
  exact h

theorem suzukiDF6D4FixedGridShard120EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard120EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 120 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 120 k) := by
    rw [suzukiDF6D4FixedGridShard120EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 120 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120EvenDotSoundness i
          suzukiDF6D4FixedGridShard120EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 120 k) := by
    simpa [suzukiDF6D4FixedGridShard120EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard120EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 120 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 120) := by
    rw [suzukiDF6D4FixedGridShard120EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 120)
  rw [suzukiDF6D4FixedGridShard120EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard120EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard120EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard120EvenDotSoundness i
            suzukiDF6D4FixedGridShard120EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard120EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard120OddComparison_eq_live :
    suzukiDF6D4FixedGridShard120OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 120 k) := by
  have h := suzukiDF6D4FixedGridShard120Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard120OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 120 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard120OddCross_eq_live :
    suzukiDF6D4FixedGridShard120OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 120) := by
  have h := suzukiDF6D4FixedGridShard120Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard120OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 120)) at h
  exact h

def suzukiDF6D4FixedGridShard120OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard120OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard120OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard120OddDotSoundness i.val
      suzukiDF6D4FixedGridShard120OddComparisonData)

theorem suzukiDF6D4FixedGridShard120OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard120OddSolveData =
      suzukiDF6D4FixedGridShard120OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard120Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard120OddSolveData =
    suzukiDF6D4FixedGridShard120OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard120OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard120OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 120 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 120 k) := by
    rw [suzukiDF6D4FixedGridShard120OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 120 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120OddDotSoundness i
          suzukiDF6D4FixedGridShard120OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 120 k) := by
    simpa [suzukiDF6D4FixedGridShard120OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard120OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 120 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 120) := by
    rw [suzukiDF6D4FixedGridShard120OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 120)
  rw [suzukiDF6D4FixedGridShard120OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard120OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard120OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard120OddDotSoundness i
            suzukiDF6D4FixedGridShard120OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard120OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard120EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard120EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 421) := by
  have h := suzukiDF6D4FixedGridShard120Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard120EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 421)) at h
  exact h

theorem suzukiDF6D4FixedGridShard120EvenFull_eq_live :
    suzukiDF6D4FixedGridShard120EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 421) := by
  have h := suzukiDF6D4FixedGridShard120Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard120EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 421)) at h
  exact h

def suzukiDF6D4FixedGridShard120EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard120EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard120EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard120EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard120EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard120EvenResidualData =
      suzukiDF6D4FixedGridShard120EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard120Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard120EvenResidualData =
    suzukiDF6D4FixedGridShard120EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard120EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard120EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 421 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 421) := by
    rw [suzukiDF6D4FixedGridShard120EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 421
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120EvenDotSoundness i
          suzukiDF6D4FixedGridShard120EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 421) := by
    simpa [suzukiDF6D4FixedGridShard120EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard120EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 421) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 421) := by
    rw [suzukiDF6D4FixedGridShard120EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 421
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard120EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard120EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard120EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard120EvenDotSoundness i
            suzukiDF6D4FixedGridShard120EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard120EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard120OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard120OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 421) := by
  have h := suzukiDF6D4FixedGridShard120Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard120OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 421)) at h
  exact h

theorem suzukiDF6D4FixedGridShard120OddFull_eq_live :
    suzukiDF6D4FixedGridShard120OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 421) := by
  have h := suzukiDF6D4FixedGridShard120Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard120OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 421)) at h
  exact h

def suzukiDF6D4FixedGridShard120OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard120OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard120OddDotSoundness i.val
        suzukiDF6D4FixedGridShard120OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard120OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard120OddResidualData =
      suzukiDF6D4FixedGridShard120OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard120Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard120OddResidualData =
    suzukiDF6D4FixedGridShard120OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard120OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard120OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 421 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 421) := by
    rw [suzukiDF6D4FixedGridShard120OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 421
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120OddDotSoundness i
          suzukiDF6D4FixedGridShard120OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 421) := by
    simpa [suzukiDF6D4FixedGridShard120OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard120OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 421) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard120OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 421) := by
    rw [suzukiDF6D4FixedGridShard120OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 421
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard120OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard120OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard120OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard120OddDotSoundness i
            suzukiDF6D4FixedGridShard120OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard120OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
