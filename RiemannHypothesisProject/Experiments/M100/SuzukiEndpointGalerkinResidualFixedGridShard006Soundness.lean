import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard006Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard006Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard006EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard006EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 6 k) := by
  have h := suzukiDF6D4FixedGridShard006Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard006EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 6 k)) at h
  exact h

def suzukiDF6D4FixedGridShard006EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard006EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard006EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard006EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard006EvenComparisonData)

theorem suzukiDF6D4FixedGridShard006EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard006EvenSolveData =
      suzukiDF6D4FixedGridShard006EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard006Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard006EvenSolveData =
    suzukiDF6D4FixedGridShard006EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard006EvenCross_eq_live :
    suzukiDF6D4FixedGridShard006EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 6) := by
  have h := suzukiDF6D4FixedGridShard006Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard006EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 6)) at h
  exact h

theorem suzukiDF6D4FixedGridShard006EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard006EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 6 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 6 k) := by
    rw [suzukiDF6D4FixedGridShard006EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 6 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006EvenDotSoundness i
          suzukiDF6D4FixedGridShard006EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 6 k) := by
    simpa [suzukiDF6D4FixedGridShard006EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard006EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 6 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 6) := by
    rw [suzukiDF6D4FixedGridShard006EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 6)
  rw [suzukiDF6D4FixedGridShard006EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard006EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard006EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard006EvenDotSoundness i
            suzukiDF6D4FixedGridShard006EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard006EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard006OddComparison_eq_live :
    suzukiDF6D4FixedGridShard006OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 6 k) := by
  have h := suzukiDF6D4FixedGridShard006Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard006OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 6 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard006OddCross_eq_live :
    suzukiDF6D4FixedGridShard006OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 6) := by
  have h := suzukiDF6D4FixedGridShard006Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard006OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 6)) at h
  exact h

def suzukiDF6D4FixedGridShard006OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard006OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard006OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard006OddDotSoundness i.val
      suzukiDF6D4FixedGridShard006OddComparisonData)

theorem suzukiDF6D4FixedGridShard006OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard006OddSolveData =
      suzukiDF6D4FixedGridShard006OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard006Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard006OddSolveData =
    suzukiDF6D4FixedGridShard006OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard006OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard006OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 6 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 6 k) := by
    rw [suzukiDF6D4FixedGridShard006OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 6 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006OddDotSoundness i
          suzukiDF6D4FixedGridShard006OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 6 k) := by
    simpa [suzukiDF6D4FixedGridShard006OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard006OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 6 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 6) := by
    rw [suzukiDF6D4FixedGridShard006OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 6)
  rw [suzukiDF6D4FixedGridShard006OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard006OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard006OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard006OddDotSoundness i
            suzukiDF6D4FixedGridShard006OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard006OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard006EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard006EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 307) := by
  have h := suzukiDF6D4FixedGridShard006Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard006EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 307)) at h
  exact h

theorem suzukiDF6D4FixedGridShard006EvenFull_eq_live :
    suzukiDF6D4FixedGridShard006EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 307) := by
  have h := suzukiDF6D4FixedGridShard006Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard006EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 307)) at h
  exact h

def suzukiDF6D4FixedGridShard006EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard006EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard006EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard006EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard006EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard006EvenResidualData =
      suzukiDF6D4FixedGridShard006EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard006Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard006EvenResidualData =
    suzukiDF6D4FixedGridShard006EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard006EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard006EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 307 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 307) := by
    rw [suzukiDF6D4FixedGridShard006EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 307
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006EvenDotSoundness i
          suzukiDF6D4FixedGridShard006EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 307) := by
    simpa [suzukiDF6D4FixedGridShard006EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard006EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 307) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 307) := by
    rw [suzukiDF6D4FixedGridShard006EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 307
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard006EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard006EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard006EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard006EvenDotSoundness i
            suzukiDF6D4FixedGridShard006EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard006EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard006OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard006OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 307) := by
  have h := suzukiDF6D4FixedGridShard006Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard006OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 307)) at h
  exact h

theorem suzukiDF6D4FixedGridShard006OddFull_eq_live :
    suzukiDF6D4FixedGridShard006OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 307) := by
  have h := suzukiDF6D4FixedGridShard006Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard006OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 307)) at h
  exact h

def suzukiDF6D4FixedGridShard006OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard006OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard006OddDotSoundness i.val
        suzukiDF6D4FixedGridShard006OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard006OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard006OddResidualData =
      suzukiDF6D4FixedGridShard006OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard006Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard006OddResidualData =
    suzukiDF6D4FixedGridShard006OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard006OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard006OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 307 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 307) := by
    rw [suzukiDF6D4FixedGridShard006OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 307
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006OddDotSoundness i
          suzukiDF6D4FixedGridShard006OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 307) := by
    simpa [suzukiDF6D4FixedGridShard006OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard006OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 307) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard006OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 307) := by
    rw [suzukiDF6D4FixedGridShard006OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 307
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard006OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard006OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard006OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard006OddDotSoundness i
            suzukiDF6D4FixedGridShard006OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard006OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
