import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard070Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard070Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard070EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard070EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 70 k) := by
  have h := suzukiDF6D4FixedGridShard070Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard070EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 70 k)) at h
  exact h

def suzukiDF6D4FixedGridShard070EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard070EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard070EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard070EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard070EvenComparisonData)

theorem suzukiDF6D4FixedGridShard070EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard070EvenSolveData =
      suzukiDF6D4FixedGridShard070EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard070Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard070EvenSolveData =
    suzukiDF6D4FixedGridShard070EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard070EvenCross_eq_live :
    suzukiDF6D4FixedGridShard070EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 70) := by
  have h := suzukiDF6D4FixedGridShard070Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard070EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 70)) at h
  exact h

theorem suzukiDF6D4FixedGridShard070EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard070EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 70 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 70 k) := by
    rw [suzukiDF6D4FixedGridShard070EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 70 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070EvenDotSoundness i
          suzukiDF6D4FixedGridShard070EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 70 k) := by
    simpa [suzukiDF6D4FixedGridShard070EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard070EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 70 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 70) := by
    rw [suzukiDF6D4FixedGridShard070EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 70)
  rw [suzukiDF6D4FixedGridShard070EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard070EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard070EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard070EvenDotSoundness i
            suzukiDF6D4FixedGridShard070EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard070EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard070OddComparison_eq_live :
    suzukiDF6D4FixedGridShard070OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 70 k) := by
  have h := suzukiDF6D4FixedGridShard070Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard070OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 70 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard070OddCross_eq_live :
    suzukiDF6D4FixedGridShard070OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 70) := by
  have h := suzukiDF6D4FixedGridShard070Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard070OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 70)) at h
  exact h

def suzukiDF6D4FixedGridShard070OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard070OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard070OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard070OddDotSoundness i.val
      suzukiDF6D4FixedGridShard070OddComparisonData)

theorem suzukiDF6D4FixedGridShard070OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard070OddSolveData =
      suzukiDF6D4FixedGridShard070OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard070Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard070OddSolveData =
    suzukiDF6D4FixedGridShard070OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard070OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard070OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 70 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 70 k) := by
    rw [suzukiDF6D4FixedGridShard070OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 70 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070OddDotSoundness i
          suzukiDF6D4FixedGridShard070OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 70 k) := by
    simpa [suzukiDF6D4FixedGridShard070OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard070OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 70 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 70) := by
    rw [suzukiDF6D4FixedGridShard070OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 70)
  rw [suzukiDF6D4FixedGridShard070OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard070OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard070OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard070OddDotSoundness i
            suzukiDF6D4FixedGridShard070OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard070OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard070EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard070EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 371) := by
  have h := suzukiDF6D4FixedGridShard070Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard070EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 371)) at h
  exact h

theorem suzukiDF6D4FixedGridShard070EvenFull_eq_live :
    suzukiDF6D4FixedGridShard070EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 371) := by
  have h := suzukiDF6D4FixedGridShard070Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard070EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 371)) at h
  exact h

def suzukiDF6D4FixedGridShard070EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard070EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard070EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard070EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard070EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard070EvenResidualData =
      suzukiDF6D4FixedGridShard070EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard070Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard070EvenResidualData =
    suzukiDF6D4FixedGridShard070EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard070EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard070EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 371 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 371) := by
    rw [suzukiDF6D4FixedGridShard070EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 371
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070EvenDotSoundness i
          suzukiDF6D4FixedGridShard070EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 371) := by
    simpa [suzukiDF6D4FixedGridShard070EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard070EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 371) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 371) := by
    rw [suzukiDF6D4FixedGridShard070EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 371
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard070EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard070EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard070EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard070EvenDotSoundness i
            suzukiDF6D4FixedGridShard070EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard070EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard070OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard070OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 371) := by
  have h := suzukiDF6D4FixedGridShard070Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard070OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 371)) at h
  exact h

theorem suzukiDF6D4FixedGridShard070OddFull_eq_live :
    suzukiDF6D4FixedGridShard070OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 371) := by
  have h := suzukiDF6D4FixedGridShard070Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard070OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 371)) at h
  exact h

def suzukiDF6D4FixedGridShard070OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard070OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard070OddDotSoundness i.val
        suzukiDF6D4FixedGridShard070OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard070OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard070OddResidualData =
      suzukiDF6D4FixedGridShard070OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard070Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard070OddResidualData =
    suzukiDF6D4FixedGridShard070OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard070OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard070OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 371 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 371) := by
    rw [suzukiDF6D4FixedGridShard070OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 371
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070OddDotSoundness i
          suzukiDF6D4FixedGridShard070OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 371) := by
    simpa [suzukiDF6D4FixedGridShard070OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard070OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 371) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard070OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 371) := by
    rw [suzukiDF6D4FixedGridShard070OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 371
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard070OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard070OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard070OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard070OddDotSoundness i
            suzukiDF6D4FixedGridShard070OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard070OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
