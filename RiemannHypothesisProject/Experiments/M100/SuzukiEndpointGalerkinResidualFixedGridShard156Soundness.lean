import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard156Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard156Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard156EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard156EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 156 k) := by
  have h := suzukiDF6D4FixedGridShard156Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard156EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 156 k)) at h
  exact h

def suzukiDF6D4FixedGridShard156EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard156EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard156EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard156EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard156EvenComparisonData)

theorem suzukiDF6D4FixedGridShard156EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard156EvenSolveData =
      suzukiDF6D4FixedGridShard156EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard156Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard156EvenSolveData =
    suzukiDF6D4FixedGridShard156EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard156EvenCross_eq_live :
    suzukiDF6D4FixedGridShard156EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 156) := by
  have h := suzukiDF6D4FixedGridShard156Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard156EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 156)) at h
  exact h

theorem suzukiDF6D4FixedGridShard156EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard156EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 156 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 156 k) := by
    rw [suzukiDF6D4FixedGridShard156EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 156 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156EvenDotSoundness i
          suzukiDF6D4FixedGridShard156EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 156 k) := by
    simpa [suzukiDF6D4FixedGridShard156EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard156EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 156 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 156) := by
    rw [suzukiDF6D4FixedGridShard156EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 156)
  rw [suzukiDF6D4FixedGridShard156EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard156EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard156EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard156EvenDotSoundness i
            suzukiDF6D4FixedGridShard156EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard156EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard156OddComparison_eq_live :
    suzukiDF6D4FixedGridShard156OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 156 k) := by
  have h := suzukiDF6D4FixedGridShard156Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard156OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 156 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard156OddCross_eq_live :
    suzukiDF6D4FixedGridShard156OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 156) := by
  have h := suzukiDF6D4FixedGridShard156Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard156OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 156)) at h
  exact h

def suzukiDF6D4FixedGridShard156OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard156OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard156OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard156OddDotSoundness i.val
      suzukiDF6D4FixedGridShard156OddComparisonData)

theorem suzukiDF6D4FixedGridShard156OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard156OddSolveData =
      suzukiDF6D4FixedGridShard156OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard156Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard156OddSolveData =
    suzukiDF6D4FixedGridShard156OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard156OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard156OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 156 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 156 k) := by
    rw [suzukiDF6D4FixedGridShard156OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 156 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156OddDotSoundness i
          suzukiDF6D4FixedGridShard156OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 156 k) := by
    simpa [suzukiDF6D4FixedGridShard156OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard156OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 156 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 156) := by
    rw [suzukiDF6D4FixedGridShard156OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 156)
  rw [suzukiDF6D4FixedGridShard156OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard156OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard156OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard156OddDotSoundness i
            suzukiDF6D4FixedGridShard156OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard156OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard156EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard156EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 457) := by
  have h := suzukiDF6D4FixedGridShard156Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard156EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 457)) at h
  exact h

theorem suzukiDF6D4FixedGridShard156EvenFull_eq_live :
    suzukiDF6D4FixedGridShard156EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 457) := by
  have h := suzukiDF6D4FixedGridShard156Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard156EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 457)) at h
  exact h

def suzukiDF6D4FixedGridShard156EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard156EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard156EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard156EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard156EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard156EvenResidualData =
      suzukiDF6D4FixedGridShard156EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard156Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard156EvenResidualData =
    suzukiDF6D4FixedGridShard156EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard156EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard156EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 457 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 457) := by
    rw [suzukiDF6D4FixedGridShard156EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 457
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156EvenDotSoundness i
          suzukiDF6D4FixedGridShard156EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 457) := by
    simpa [suzukiDF6D4FixedGridShard156EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard156EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 457) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 457) := by
    rw [suzukiDF6D4FixedGridShard156EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 457
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard156EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard156EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard156EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard156EvenDotSoundness i
            suzukiDF6D4FixedGridShard156EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard156EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard156OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard156OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 457) := by
  have h := suzukiDF6D4FixedGridShard156Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard156OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 457)) at h
  exact h

theorem suzukiDF6D4FixedGridShard156OddFull_eq_live :
    suzukiDF6D4FixedGridShard156OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 457) := by
  have h := suzukiDF6D4FixedGridShard156Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard156OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 457)) at h
  exact h

def suzukiDF6D4FixedGridShard156OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard156OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard156OddDotSoundness i.val
        suzukiDF6D4FixedGridShard156OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard156OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard156OddResidualData =
      suzukiDF6D4FixedGridShard156OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard156Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard156OddResidualData =
    suzukiDF6D4FixedGridShard156OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard156OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard156OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 457 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 457) := by
    rw [suzukiDF6D4FixedGridShard156OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 457
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156OddDotSoundness i
          suzukiDF6D4FixedGridShard156OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 457) := by
    simpa [suzukiDF6D4FixedGridShard156OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard156OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 457) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard156OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 457) := by
    rw [suzukiDF6D4FixedGridShard156OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 457
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard156OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard156OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard156OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard156OddDotSoundness i
            suzukiDF6D4FixedGridShard156OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard156OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
