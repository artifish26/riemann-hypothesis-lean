import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard009Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard009Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard009EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard009EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 9 k) := by
  have h := suzukiDF6D4FixedGridShard009Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard009EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 9 k)) at h
  exact h

def suzukiDF6D4FixedGridShard009EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard009EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard009EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard009EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard009EvenComparisonData)

theorem suzukiDF6D4FixedGridShard009EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard009EvenSolveData =
      suzukiDF6D4FixedGridShard009EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard009Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard009EvenSolveData =
    suzukiDF6D4FixedGridShard009EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard009EvenCross_eq_live :
    suzukiDF6D4FixedGridShard009EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 9) := by
  have h := suzukiDF6D4FixedGridShard009Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard009EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 9)) at h
  exact h

theorem suzukiDF6D4FixedGridShard009EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard009EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 9 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 9 k) := by
    rw [suzukiDF6D4FixedGridShard009EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 9 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009EvenDotSoundness i
          suzukiDF6D4FixedGridShard009EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 9 k) := by
    simpa [suzukiDF6D4FixedGridShard009EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard009EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 9 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 9) := by
    rw [suzukiDF6D4FixedGridShard009EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 9)
  rw [suzukiDF6D4FixedGridShard009EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard009EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard009EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard009EvenDotSoundness i
            suzukiDF6D4FixedGridShard009EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard009EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard009OddComparison_eq_live :
    suzukiDF6D4FixedGridShard009OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 9 k) := by
  have h := suzukiDF6D4FixedGridShard009Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard009OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 9 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard009OddCross_eq_live :
    suzukiDF6D4FixedGridShard009OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 9) := by
  have h := suzukiDF6D4FixedGridShard009Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard009OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 9)) at h
  exact h

def suzukiDF6D4FixedGridShard009OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard009OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard009OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard009OddDotSoundness i.val
      suzukiDF6D4FixedGridShard009OddComparisonData)

theorem suzukiDF6D4FixedGridShard009OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard009OddSolveData =
      suzukiDF6D4FixedGridShard009OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard009Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard009OddSolveData =
    suzukiDF6D4FixedGridShard009OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard009OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard009OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 9 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 9 k) := by
    rw [suzukiDF6D4FixedGridShard009OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 9 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009OddDotSoundness i
          suzukiDF6D4FixedGridShard009OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 9 k) := by
    simpa [suzukiDF6D4FixedGridShard009OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard009OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 9 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 9) := by
    rw [suzukiDF6D4FixedGridShard009OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 9)
  rw [suzukiDF6D4FixedGridShard009OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard009OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard009OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard009OddDotSoundness i
            suzukiDF6D4FixedGridShard009OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard009OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard009EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard009EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 310) := by
  have h := suzukiDF6D4FixedGridShard009Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard009EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 310)) at h
  exact h

theorem suzukiDF6D4FixedGridShard009EvenFull_eq_live :
    suzukiDF6D4FixedGridShard009EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 310) := by
  have h := suzukiDF6D4FixedGridShard009Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard009EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 310)) at h
  exact h

def suzukiDF6D4FixedGridShard009EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard009EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard009EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard009EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard009EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard009EvenResidualData =
      suzukiDF6D4FixedGridShard009EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard009Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard009EvenResidualData =
    suzukiDF6D4FixedGridShard009EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard009EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard009EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 310 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 310) := by
    rw [suzukiDF6D4FixedGridShard009EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 310
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009EvenDotSoundness i
          suzukiDF6D4FixedGridShard009EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 310) := by
    simpa [suzukiDF6D4FixedGridShard009EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard009EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 310) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 310) := by
    rw [suzukiDF6D4FixedGridShard009EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 310
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard009EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard009EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard009EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard009EvenDotSoundness i
            suzukiDF6D4FixedGridShard009EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard009EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard009OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard009OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 310) := by
  have h := suzukiDF6D4FixedGridShard009Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard009OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 310)) at h
  exact h

theorem suzukiDF6D4FixedGridShard009OddFull_eq_live :
    suzukiDF6D4FixedGridShard009OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 310) := by
  have h := suzukiDF6D4FixedGridShard009Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard009OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 310)) at h
  exact h

def suzukiDF6D4FixedGridShard009OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard009OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard009OddDotSoundness i.val
        suzukiDF6D4FixedGridShard009OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard009OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard009OddResidualData =
      suzukiDF6D4FixedGridShard009OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard009Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard009OddResidualData =
    suzukiDF6D4FixedGridShard009OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard009OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard009OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 310 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 310) := by
    rw [suzukiDF6D4FixedGridShard009OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 310
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009OddDotSoundness i
          suzukiDF6D4FixedGridShard009OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 310) := by
    simpa [suzukiDF6D4FixedGridShard009OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard009OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 310) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard009OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 310) := by
    rw [suzukiDF6D4FixedGridShard009OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 310
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard009OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard009OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard009OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard009OddDotSoundness i
            suzukiDF6D4FixedGridShard009OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard009OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
