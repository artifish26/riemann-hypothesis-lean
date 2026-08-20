import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard014Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard014Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard014EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard014EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 14 k) := by
  have h := suzukiDF6D4FixedGridShard014Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard014EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 14 k)) at h
  exact h

def suzukiDF6D4FixedGridShard014EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard014EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard014EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard014EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard014EvenComparisonData)

theorem suzukiDF6D4FixedGridShard014EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard014EvenSolveData =
      suzukiDF6D4FixedGridShard014EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard014Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard014EvenSolveData =
    suzukiDF6D4FixedGridShard014EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard014EvenCross_eq_live :
    suzukiDF6D4FixedGridShard014EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 14) := by
  have h := suzukiDF6D4FixedGridShard014Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard014EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 14)) at h
  exact h

theorem suzukiDF6D4FixedGridShard014EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard014EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 14 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 14 k) := by
    rw [suzukiDF6D4FixedGridShard014EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 14 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014EvenDotSoundness i
          suzukiDF6D4FixedGridShard014EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 14 k) := by
    simpa [suzukiDF6D4FixedGridShard014EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard014EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 14 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 14) := by
    rw [suzukiDF6D4FixedGridShard014EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 14)
  rw [suzukiDF6D4FixedGridShard014EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard014EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard014EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard014EvenDotSoundness i
            suzukiDF6D4FixedGridShard014EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard014EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard014OddComparison_eq_live :
    suzukiDF6D4FixedGridShard014OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 14 k) := by
  have h := suzukiDF6D4FixedGridShard014Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard014OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 14 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard014OddCross_eq_live :
    suzukiDF6D4FixedGridShard014OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 14) := by
  have h := suzukiDF6D4FixedGridShard014Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard014OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 14)) at h
  exact h

def suzukiDF6D4FixedGridShard014OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard014OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard014OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard014OddDotSoundness i.val
      suzukiDF6D4FixedGridShard014OddComparisonData)

theorem suzukiDF6D4FixedGridShard014OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard014OddSolveData =
      suzukiDF6D4FixedGridShard014OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard014Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard014OddSolveData =
    suzukiDF6D4FixedGridShard014OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard014OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard014OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 14 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 14 k) := by
    rw [suzukiDF6D4FixedGridShard014OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 14 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014OddDotSoundness i
          suzukiDF6D4FixedGridShard014OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 14 k) := by
    simpa [suzukiDF6D4FixedGridShard014OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard014OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 14 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 14) := by
    rw [suzukiDF6D4FixedGridShard014OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 14)
  rw [suzukiDF6D4FixedGridShard014OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard014OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard014OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard014OddDotSoundness i
            suzukiDF6D4FixedGridShard014OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard014OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard014EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard014EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 315) := by
  have h := suzukiDF6D4FixedGridShard014Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard014EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 315)) at h
  exact h

theorem suzukiDF6D4FixedGridShard014EvenFull_eq_live :
    suzukiDF6D4FixedGridShard014EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 315) := by
  have h := suzukiDF6D4FixedGridShard014Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard014EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 315)) at h
  exact h

def suzukiDF6D4FixedGridShard014EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard014EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard014EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard014EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard014EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard014EvenResidualData =
      suzukiDF6D4FixedGridShard014EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard014Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard014EvenResidualData =
    suzukiDF6D4FixedGridShard014EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard014EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard014EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 315 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 315) := by
    rw [suzukiDF6D4FixedGridShard014EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 315
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014EvenDotSoundness i
          suzukiDF6D4FixedGridShard014EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 315) := by
    simpa [suzukiDF6D4FixedGridShard014EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard014EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 315) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 315) := by
    rw [suzukiDF6D4FixedGridShard014EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 315
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard014EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard014EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard014EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard014EvenDotSoundness i
            suzukiDF6D4FixedGridShard014EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard014EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard014OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard014OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 315) := by
  have h := suzukiDF6D4FixedGridShard014Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard014OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 315)) at h
  exact h

theorem suzukiDF6D4FixedGridShard014OddFull_eq_live :
    suzukiDF6D4FixedGridShard014OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 315) := by
  have h := suzukiDF6D4FixedGridShard014Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard014OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 315)) at h
  exact h

def suzukiDF6D4FixedGridShard014OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard014OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard014OddDotSoundness i.val
        suzukiDF6D4FixedGridShard014OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard014OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard014OddResidualData =
      suzukiDF6D4FixedGridShard014OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard014Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard014OddResidualData =
    suzukiDF6D4FixedGridShard014OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard014OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard014OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 315 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 315) := by
    rw [suzukiDF6D4FixedGridShard014OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 315
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014OddDotSoundness i
          suzukiDF6D4FixedGridShard014OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 315) := by
    simpa [suzukiDF6D4FixedGridShard014OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard014OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 315) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard014OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 315) := by
    rw [suzukiDF6D4FixedGridShard014OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 315
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard014OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard014OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard014OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard014OddDotSoundness i
            suzukiDF6D4FixedGridShard014OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard014OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
