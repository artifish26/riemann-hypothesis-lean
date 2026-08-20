import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard035Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard035Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard035EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard035EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 35 k) := by
  have h := suzukiDF6D4FixedGridShard035Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard035EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 35 k)) at h
  exact h

def suzukiDF6D4FixedGridShard035EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard035EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard035EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard035EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard035EvenComparisonData)

theorem suzukiDF6D4FixedGridShard035EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard035EvenSolveData =
      suzukiDF6D4FixedGridShard035EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard035Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard035EvenSolveData =
    suzukiDF6D4FixedGridShard035EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard035EvenCross_eq_live :
    suzukiDF6D4FixedGridShard035EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 35) := by
  have h := suzukiDF6D4FixedGridShard035Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard035EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 35)) at h
  exact h

theorem suzukiDF6D4FixedGridShard035EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard035EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 35 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 35 k) := by
    rw [suzukiDF6D4FixedGridShard035EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 35 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035EvenDotSoundness i
          suzukiDF6D4FixedGridShard035EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 35 k) := by
    simpa [suzukiDF6D4FixedGridShard035EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard035EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 35 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 35) := by
    rw [suzukiDF6D4FixedGridShard035EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 35)
  rw [suzukiDF6D4FixedGridShard035EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard035EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard035EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard035EvenDotSoundness i
            suzukiDF6D4FixedGridShard035EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard035EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard035OddComparison_eq_live :
    suzukiDF6D4FixedGridShard035OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 35 k) := by
  have h := suzukiDF6D4FixedGridShard035Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard035OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 35 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard035OddCross_eq_live :
    suzukiDF6D4FixedGridShard035OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 35) := by
  have h := suzukiDF6D4FixedGridShard035Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard035OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 35)) at h
  exact h

def suzukiDF6D4FixedGridShard035OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard035OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard035OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard035OddDotSoundness i.val
      suzukiDF6D4FixedGridShard035OddComparisonData)

theorem suzukiDF6D4FixedGridShard035OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard035OddSolveData =
      suzukiDF6D4FixedGridShard035OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard035Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard035OddSolveData =
    suzukiDF6D4FixedGridShard035OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard035OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard035OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 35 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 35 k) := by
    rw [suzukiDF6D4FixedGridShard035OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 35 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035OddDotSoundness i
          suzukiDF6D4FixedGridShard035OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 35 k) := by
    simpa [suzukiDF6D4FixedGridShard035OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard035OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 35 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 35) := by
    rw [suzukiDF6D4FixedGridShard035OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 35)
  rw [suzukiDF6D4FixedGridShard035OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard035OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard035OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard035OddDotSoundness i
            suzukiDF6D4FixedGridShard035OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard035OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard035EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard035EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 336) := by
  have h := suzukiDF6D4FixedGridShard035Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard035EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 336)) at h
  exact h

theorem suzukiDF6D4FixedGridShard035EvenFull_eq_live :
    suzukiDF6D4FixedGridShard035EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 336) := by
  have h := suzukiDF6D4FixedGridShard035Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard035EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 336)) at h
  exact h

def suzukiDF6D4FixedGridShard035EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard035EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard035EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard035EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard035EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard035EvenResidualData =
      suzukiDF6D4FixedGridShard035EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard035Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard035EvenResidualData =
    suzukiDF6D4FixedGridShard035EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard035EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard035EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 336 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 336) := by
    rw [suzukiDF6D4FixedGridShard035EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 336
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035EvenDotSoundness i
          suzukiDF6D4FixedGridShard035EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 336) := by
    simpa [suzukiDF6D4FixedGridShard035EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard035EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 336) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 336) := by
    rw [suzukiDF6D4FixedGridShard035EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 336
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard035EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard035EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard035EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard035EvenDotSoundness i
            suzukiDF6D4FixedGridShard035EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard035EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard035OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard035OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 336) := by
  have h := suzukiDF6D4FixedGridShard035Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard035OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 336)) at h
  exact h

theorem suzukiDF6D4FixedGridShard035OddFull_eq_live :
    suzukiDF6D4FixedGridShard035OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 336) := by
  have h := suzukiDF6D4FixedGridShard035Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard035OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 336)) at h
  exact h

def suzukiDF6D4FixedGridShard035OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard035OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard035OddDotSoundness i.val
        suzukiDF6D4FixedGridShard035OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard035OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard035OddResidualData =
      suzukiDF6D4FixedGridShard035OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard035Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard035OddResidualData =
    suzukiDF6D4FixedGridShard035OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard035OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard035OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 336 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 336) := by
    rw [suzukiDF6D4FixedGridShard035OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 336
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035OddDotSoundness i
          suzukiDF6D4FixedGridShard035OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 336) := by
    simpa [suzukiDF6D4FixedGridShard035OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard035OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 336) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard035OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 336) := by
    rw [suzukiDF6D4FixedGridShard035OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 336
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard035OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard035OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard035OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard035OddDotSoundness i
            suzukiDF6D4FixedGridShard035OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard035OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
