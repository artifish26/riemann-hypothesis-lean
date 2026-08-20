import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard124Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard124Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard124EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard124EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 124 k) := by
  have h := suzukiDF6D4FixedGridShard124Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard124EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 124 k)) at h
  exact h

def suzukiDF6D4FixedGridShard124EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard124EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard124EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard124EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard124EvenComparisonData)

theorem suzukiDF6D4FixedGridShard124EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard124EvenSolveData =
      suzukiDF6D4FixedGridShard124EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard124Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard124EvenSolveData =
    suzukiDF6D4FixedGridShard124EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard124EvenCross_eq_live :
    suzukiDF6D4FixedGridShard124EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 124) := by
  have h := suzukiDF6D4FixedGridShard124Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard124EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 124)) at h
  exact h

theorem suzukiDF6D4FixedGridShard124EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard124EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 124 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 124 k) := by
    rw [suzukiDF6D4FixedGridShard124EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 124 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124EvenDotSoundness i
          suzukiDF6D4FixedGridShard124EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 124 k) := by
    simpa [suzukiDF6D4FixedGridShard124EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard124EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 124 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 124) := by
    rw [suzukiDF6D4FixedGridShard124EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 124)
  rw [suzukiDF6D4FixedGridShard124EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard124EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard124EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard124EvenDotSoundness i
            suzukiDF6D4FixedGridShard124EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard124EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard124OddComparison_eq_live :
    suzukiDF6D4FixedGridShard124OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 124 k) := by
  have h := suzukiDF6D4FixedGridShard124Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard124OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 124 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard124OddCross_eq_live :
    suzukiDF6D4FixedGridShard124OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 124) := by
  have h := suzukiDF6D4FixedGridShard124Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard124OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 124)) at h
  exact h

def suzukiDF6D4FixedGridShard124OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard124OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard124OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard124OddDotSoundness i.val
      suzukiDF6D4FixedGridShard124OddComparisonData)

theorem suzukiDF6D4FixedGridShard124OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard124OddSolveData =
      suzukiDF6D4FixedGridShard124OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard124Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard124OddSolveData =
    suzukiDF6D4FixedGridShard124OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard124OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard124OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 124 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 124 k) := by
    rw [suzukiDF6D4FixedGridShard124OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 124 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124OddDotSoundness i
          suzukiDF6D4FixedGridShard124OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 124 k) := by
    simpa [suzukiDF6D4FixedGridShard124OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard124OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 124 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 124) := by
    rw [suzukiDF6D4FixedGridShard124OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 124)
  rw [suzukiDF6D4FixedGridShard124OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard124OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard124OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard124OddDotSoundness i
            suzukiDF6D4FixedGridShard124OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard124OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard124EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard124EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 425) := by
  have h := suzukiDF6D4FixedGridShard124Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard124EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 425)) at h
  exact h

theorem suzukiDF6D4FixedGridShard124EvenFull_eq_live :
    suzukiDF6D4FixedGridShard124EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 425) := by
  have h := suzukiDF6D4FixedGridShard124Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard124EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 425)) at h
  exact h

def suzukiDF6D4FixedGridShard124EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard124EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard124EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard124EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard124EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard124EvenResidualData =
      suzukiDF6D4FixedGridShard124EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard124Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard124EvenResidualData =
    suzukiDF6D4FixedGridShard124EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard124EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard124EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 425 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 425) := by
    rw [suzukiDF6D4FixedGridShard124EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 425
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124EvenDotSoundness i
          suzukiDF6D4FixedGridShard124EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 425) := by
    simpa [suzukiDF6D4FixedGridShard124EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard124EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 425) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 425) := by
    rw [suzukiDF6D4FixedGridShard124EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 425
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard124EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard124EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard124EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard124EvenDotSoundness i
            suzukiDF6D4FixedGridShard124EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard124EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard124OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard124OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 425) := by
  have h := suzukiDF6D4FixedGridShard124Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard124OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 425)) at h
  exact h

theorem suzukiDF6D4FixedGridShard124OddFull_eq_live :
    suzukiDF6D4FixedGridShard124OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 425) := by
  have h := suzukiDF6D4FixedGridShard124Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard124OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 425)) at h
  exact h

def suzukiDF6D4FixedGridShard124OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard124OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard124OddDotSoundness i.val
        suzukiDF6D4FixedGridShard124OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard124OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard124OddResidualData =
      suzukiDF6D4FixedGridShard124OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard124Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard124OddResidualData =
    suzukiDF6D4FixedGridShard124OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard124OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard124OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 425 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 425) := by
    rw [suzukiDF6D4FixedGridShard124OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 425
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124OddDotSoundness i
          suzukiDF6D4FixedGridShard124OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 425) := by
    simpa [suzukiDF6D4FixedGridShard124OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard124OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 425) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard124OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 425) := by
    rw [suzukiDF6D4FixedGridShard124OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 425
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard124OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard124OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard124OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard124OddDotSoundness i
            suzukiDF6D4FixedGridShard124OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard124OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
