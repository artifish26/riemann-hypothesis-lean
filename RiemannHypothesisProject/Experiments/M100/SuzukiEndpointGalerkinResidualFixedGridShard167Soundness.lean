import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard167Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard167Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard167EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard167EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 167 k) := by
  have h := suzukiDF6D4FixedGridShard167Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard167EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 167 k)) at h
  exact h

def suzukiDF6D4FixedGridShard167EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard167EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard167EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard167EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard167EvenComparisonData)

theorem suzukiDF6D4FixedGridShard167EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard167EvenSolveData =
      suzukiDF6D4FixedGridShard167EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard167Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard167EvenSolveData =
    suzukiDF6D4FixedGridShard167EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard167EvenCross_eq_live :
    suzukiDF6D4FixedGridShard167EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 167) := by
  have h := suzukiDF6D4FixedGridShard167Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard167EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 167)) at h
  exact h

theorem suzukiDF6D4FixedGridShard167EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard167EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 167 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 167 k) := by
    rw [suzukiDF6D4FixedGridShard167EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 167 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167EvenDotSoundness i
          suzukiDF6D4FixedGridShard167EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 167 k) := by
    simpa [suzukiDF6D4FixedGridShard167EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard167EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 167 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 167) := by
    rw [suzukiDF6D4FixedGridShard167EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 167)
  rw [suzukiDF6D4FixedGridShard167EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard167EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard167EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard167EvenDotSoundness i
            suzukiDF6D4FixedGridShard167EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard167EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard167OddComparison_eq_live :
    suzukiDF6D4FixedGridShard167OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 167 k) := by
  have h := suzukiDF6D4FixedGridShard167Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard167OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 167 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard167OddCross_eq_live :
    suzukiDF6D4FixedGridShard167OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 167) := by
  have h := suzukiDF6D4FixedGridShard167Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard167OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 167)) at h
  exact h

def suzukiDF6D4FixedGridShard167OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard167OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard167OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard167OddDotSoundness i.val
      suzukiDF6D4FixedGridShard167OddComparisonData)

theorem suzukiDF6D4FixedGridShard167OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard167OddSolveData =
      suzukiDF6D4FixedGridShard167OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard167Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard167OddSolveData =
    suzukiDF6D4FixedGridShard167OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard167OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard167OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 167 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 167 k) := by
    rw [suzukiDF6D4FixedGridShard167OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 167 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167OddDotSoundness i
          suzukiDF6D4FixedGridShard167OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 167 k) := by
    simpa [suzukiDF6D4FixedGridShard167OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard167OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 167 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 167) := by
    rw [suzukiDF6D4FixedGridShard167OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 167)
  rw [suzukiDF6D4FixedGridShard167OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard167OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard167OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard167OddDotSoundness i
            suzukiDF6D4FixedGridShard167OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard167OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard167EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard167EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 468) := by
  have h := suzukiDF6D4FixedGridShard167Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard167EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 468)) at h
  exact h

theorem suzukiDF6D4FixedGridShard167EvenFull_eq_live :
    suzukiDF6D4FixedGridShard167EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 468) := by
  have h := suzukiDF6D4FixedGridShard167Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard167EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 468)) at h
  exact h

def suzukiDF6D4FixedGridShard167EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard167EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard167EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard167EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard167EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard167EvenResidualData =
      suzukiDF6D4FixedGridShard167EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard167Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard167EvenResidualData =
    suzukiDF6D4FixedGridShard167EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard167EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard167EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 468 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 468) := by
    rw [suzukiDF6D4FixedGridShard167EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 468
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167EvenDotSoundness i
          suzukiDF6D4FixedGridShard167EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 468) := by
    simpa [suzukiDF6D4FixedGridShard167EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard167EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 468) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 468) := by
    rw [suzukiDF6D4FixedGridShard167EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 468
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard167EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard167EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard167EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard167EvenDotSoundness i
            suzukiDF6D4FixedGridShard167EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard167EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard167OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard167OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 468) := by
  have h := suzukiDF6D4FixedGridShard167Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard167OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 468)) at h
  exact h

theorem suzukiDF6D4FixedGridShard167OddFull_eq_live :
    suzukiDF6D4FixedGridShard167OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 468) := by
  have h := suzukiDF6D4FixedGridShard167Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard167OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 468)) at h
  exact h

def suzukiDF6D4FixedGridShard167OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard167OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard167OddDotSoundness i.val
        suzukiDF6D4FixedGridShard167OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard167OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard167OddResidualData =
      suzukiDF6D4FixedGridShard167OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard167Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard167OddResidualData =
    suzukiDF6D4FixedGridShard167OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard167OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard167OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 468 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 468) := by
    rw [suzukiDF6D4FixedGridShard167OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 468
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167OddDotSoundness i
          suzukiDF6D4FixedGridShard167OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 468) := by
    simpa [suzukiDF6D4FixedGridShard167OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard167OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 468) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard167OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 468) := by
    rw [suzukiDF6D4FixedGridShard167OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 468
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard167OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard167OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard167OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard167OddDotSoundness i
            suzukiDF6D4FixedGridShard167OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard167OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
