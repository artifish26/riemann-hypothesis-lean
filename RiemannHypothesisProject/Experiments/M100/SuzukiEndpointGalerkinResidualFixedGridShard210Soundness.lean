import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard210Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard210Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard210EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard210EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 210 k) := by
  have h := suzukiDF6D4FixedGridShard210Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard210EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 210 k)) at h
  exact h

def suzukiDF6D4FixedGridShard210EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard210EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard210EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard210EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard210EvenComparisonData)

theorem suzukiDF6D4FixedGridShard210EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard210EvenSolveData =
      suzukiDF6D4FixedGridShard210EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard210Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard210EvenSolveData =
    suzukiDF6D4FixedGridShard210EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard210EvenCross_eq_live :
    suzukiDF6D4FixedGridShard210EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 210) := by
  have h := suzukiDF6D4FixedGridShard210Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard210EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 210)) at h
  exact h

theorem suzukiDF6D4FixedGridShard210EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard210EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 210 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 210 k) := by
    rw [suzukiDF6D4FixedGridShard210EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 210 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210EvenDotSoundness i
          suzukiDF6D4FixedGridShard210EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 210 k) := by
    simpa [suzukiDF6D4FixedGridShard210EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard210EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 210 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 210) := by
    rw [suzukiDF6D4FixedGridShard210EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 210)
  rw [suzukiDF6D4FixedGridShard210EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard210EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard210EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard210EvenDotSoundness i
            suzukiDF6D4FixedGridShard210EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard210EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard210OddComparison_eq_live :
    suzukiDF6D4FixedGridShard210OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 210 k) := by
  have h := suzukiDF6D4FixedGridShard210Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard210OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 210 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard210OddCross_eq_live :
    suzukiDF6D4FixedGridShard210OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 210) := by
  have h := suzukiDF6D4FixedGridShard210Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard210OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 210)) at h
  exact h

def suzukiDF6D4FixedGridShard210OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard210OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard210OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard210OddDotSoundness i.val
      suzukiDF6D4FixedGridShard210OddComparisonData)

theorem suzukiDF6D4FixedGridShard210OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard210OddSolveData =
      suzukiDF6D4FixedGridShard210OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard210Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard210OddSolveData =
    suzukiDF6D4FixedGridShard210OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard210OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard210OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 210 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 210 k) := by
    rw [suzukiDF6D4FixedGridShard210OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 210 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210OddDotSoundness i
          suzukiDF6D4FixedGridShard210OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 210 k) := by
    simpa [suzukiDF6D4FixedGridShard210OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard210OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 210 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 210) := by
    rw [suzukiDF6D4FixedGridShard210OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 210)
  rw [suzukiDF6D4FixedGridShard210OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard210OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard210OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard210OddDotSoundness i
            suzukiDF6D4FixedGridShard210OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard210OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard210EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard210EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 511) := by
  have h := suzukiDF6D4FixedGridShard210Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard210EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 511)) at h
  exact h

theorem suzukiDF6D4FixedGridShard210EvenFull_eq_live :
    suzukiDF6D4FixedGridShard210EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 511) := by
  have h := suzukiDF6D4FixedGridShard210Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard210EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 511)) at h
  exact h

def suzukiDF6D4FixedGridShard210EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard210EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard210EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard210EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard210EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard210EvenResidualData =
      suzukiDF6D4FixedGridShard210EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard210Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard210EvenResidualData =
    suzukiDF6D4FixedGridShard210EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard210EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard210EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 511 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 511) := by
    rw [suzukiDF6D4FixedGridShard210EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 511
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210EvenDotSoundness i
          suzukiDF6D4FixedGridShard210EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 511) := by
    simpa [suzukiDF6D4FixedGridShard210EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard210EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 511) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 511) := by
    rw [suzukiDF6D4FixedGridShard210EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 511
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard210EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard210EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard210EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard210EvenDotSoundness i
            suzukiDF6D4FixedGridShard210EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard210EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard210OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard210OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 511) := by
  have h := suzukiDF6D4FixedGridShard210Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard210OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 511)) at h
  exact h

theorem suzukiDF6D4FixedGridShard210OddFull_eq_live :
    suzukiDF6D4FixedGridShard210OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 511) := by
  have h := suzukiDF6D4FixedGridShard210Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard210OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 511)) at h
  exact h

def suzukiDF6D4FixedGridShard210OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard210OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard210OddDotSoundness i.val
        suzukiDF6D4FixedGridShard210OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard210OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard210OddResidualData =
      suzukiDF6D4FixedGridShard210OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard210Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard210OddResidualData =
    suzukiDF6D4FixedGridShard210OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard210OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard210OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 511 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 511) := by
    rw [suzukiDF6D4FixedGridShard210OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 511
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210OddDotSoundness i
          suzukiDF6D4FixedGridShard210OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 511) := by
    simpa [suzukiDF6D4FixedGridShard210OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard210OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 511) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard210OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 511) := by
    rw [suzukiDF6D4FixedGridShard210OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 511
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard210OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard210OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard210OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard210OddDotSoundness i
            suzukiDF6D4FixedGridShard210OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard210OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
