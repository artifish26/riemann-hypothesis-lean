import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard092Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard092Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard092EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard092EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 92 k) := by
  have h := suzukiDF6D4FixedGridShard092Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard092EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 92 k)) at h
  exact h

def suzukiDF6D4FixedGridShard092EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard092EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard092EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard092EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard092EvenComparisonData)

theorem suzukiDF6D4FixedGridShard092EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard092EvenSolveData =
      suzukiDF6D4FixedGridShard092EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard092Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard092EvenSolveData =
    suzukiDF6D4FixedGridShard092EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard092EvenCross_eq_live :
    suzukiDF6D4FixedGridShard092EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 92) := by
  have h := suzukiDF6D4FixedGridShard092Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard092EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 92)) at h
  exact h

theorem suzukiDF6D4FixedGridShard092EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard092EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 92 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 92 k) := by
    rw [suzukiDF6D4FixedGridShard092EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 92 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092EvenDotSoundness i
          suzukiDF6D4FixedGridShard092EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 92 k) := by
    simpa [suzukiDF6D4FixedGridShard092EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard092EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 92 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 92) := by
    rw [suzukiDF6D4FixedGridShard092EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 92)
  rw [suzukiDF6D4FixedGridShard092EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard092EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard092EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard092EvenDotSoundness i
            suzukiDF6D4FixedGridShard092EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard092EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard092OddComparison_eq_live :
    suzukiDF6D4FixedGridShard092OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 92 k) := by
  have h := suzukiDF6D4FixedGridShard092Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard092OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 92 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard092OddCross_eq_live :
    suzukiDF6D4FixedGridShard092OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 92) := by
  have h := suzukiDF6D4FixedGridShard092Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard092OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 92)) at h
  exact h

def suzukiDF6D4FixedGridShard092OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard092OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard092OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard092OddDotSoundness i.val
      suzukiDF6D4FixedGridShard092OddComparisonData)

theorem suzukiDF6D4FixedGridShard092OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard092OddSolveData =
      suzukiDF6D4FixedGridShard092OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard092Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard092OddSolveData =
    suzukiDF6D4FixedGridShard092OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard092OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard092OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 92 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 92 k) := by
    rw [suzukiDF6D4FixedGridShard092OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 92 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092OddDotSoundness i
          suzukiDF6D4FixedGridShard092OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 92 k) := by
    simpa [suzukiDF6D4FixedGridShard092OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard092OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 92 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 92) := by
    rw [suzukiDF6D4FixedGridShard092OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 92)
  rw [suzukiDF6D4FixedGridShard092OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard092OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard092OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard092OddDotSoundness i
            suzukiDF6D4FixedGridShard092OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard092OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard092EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard092EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 393) := by
  have h := suzukiDF6D4FixedGridShard092Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard092EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 393)) at h
  exact h

theorem suzukiDF6D4FixedGridShard092EvenFull_eq_live :
    suzukiDF6D4FixedGridShard092EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 393) := by
  have h := suzukiDF6D4FixedGridShard092Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard092EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 393)) at h
  exact h

def suzukiDF6D4FixedGridShard092EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard092EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard092EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard092EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard092EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard092EvenResidualData =
      suzukiDF6D4FixedGridShard092EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard092Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard092EvenResidualData =
    suzukiDF6D4FixedGridShard092EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard092EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard092EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 393 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 393) := by
    rw [suzukiDF6D4FixedGridShard092EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 393
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092EvenDotSoundness i
          suzukiDF6D4FixedGridShard092EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 393) := by
    simpa [suzukiDF6D4FixedGridShard092EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard092EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 393) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 393) := by
    rw [suzukiDF6D4FixedGridShard092EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 393
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard092EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard092EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard092EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard092EvenDotSoundness i
            suzukiDF6D4FixedGridShard092EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard092EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard092OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard092OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 393) := by
  have h := suzukiDF6D4FixedGridShard092Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard092OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 393)) at h
  exact h

theorem suzukiDF6D4FixedGridShard092OddFull_eq_live :
    suzukiDF6D4FixedGridShard092OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 393) := by
  have h := suzukiDF6D4FixedGridShard092Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard092OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 393)) at h
  exact h

def suzukiDF6D4FixedGridShard092OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard092OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard092OddDotSoundness i.val
        suzukiDF6D4FixedGridShard092OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard092OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard092OddResidualData =
      suzukiDF6D4FixedGridShard092OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard092Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard092OddResidualData =
    suzukiDF6D4FixedGridShard092OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard092OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard092OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 393 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 393) := by
    rw [suzukiDF6D4FixedGridShard092OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 393
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092OddDotSoundness i
          suzukiDF6D4FixedGridShard092OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 393) := by
    simpa [suzukiDF6D4FixedGridShard092OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard092OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 393) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard092OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 393) := by
    rw [suzukiDF6D4FixedGridShard092OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 393
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard092OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard092OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard092OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard092OddDotSoundness i
            suzukiDF6D4FixedGridShard092OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard092OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
