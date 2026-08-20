import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard080Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard080Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard080EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard080EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 80 k) := by
  have h := suzukiDF6D4FixedGridShard080Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard080EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 80 k)) at h
  exact h

def suzukiDF6D4FixedGridShard080EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard080EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard080EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard080EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard080EvenComparisonData)

theorem suzukiDF6D4FixedGridShard080EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard080EvenSolveData =
      suzukiDF6D4FixedGridShard080EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard080Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard080EvenSolveData =
    suzukiDF6D4FixedGridShard080EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard080EvenCross_eq_live :
    suzukiDF6D4FixedGridShard080EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 80) := by
  have h := suzukiDF6D4FixedGridShard080Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard080EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 80)) at h
  exact h

theorem suzukiDF6D4FixedGridShard080EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard080EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 80 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 80 k) := by
    rw [suzukiDF6D4FixedGridShard080EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 80 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080EvenDotSoundness i
          suzukiDF6D4FixedGridShard080EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 80 k) := by
    simpa [suzukiDF6D4FixedGridShard080EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard080EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 80 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 80) := by
    rw [suzukiDF6D4FixedGridShard080EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 80)
  rw [suzukiDF6D4FixedGridShard080EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard080EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard080EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard080EvenDotSoundness i
            suzukiDF6D4FixedGridShard080EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard080EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard080OddComparison_eq_live :
    suzukiDF6D4FixedGridShard080OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 80 k) := by
  have h := suzukiDF6D4FixedGridShard080Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard080OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 80 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard080OddCross_eq_live :
    suzukiDF6D4FixedGridShard080OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 80) := by
  have h := suzukiDF6D4FixedGridShard080Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard080OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 80)) at h
  exact h

def suzukiDF6D4FixedGridShard080OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard080OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard080OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard080OddDotSoundness i.val
      suzukiDF6D4FixedGridShard080OddComparisonData)

theorem suzukiDF6D4FixedGridShard080OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard080OddSolveData =
      suzukiDF6D4FixedGridShard080OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard080Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard080OddSolveData =
    suzukiDF6D4FixedGridShard080OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard080OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard080OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 80 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 80 k) := by
    rw [suzukiDF6D4FixedGridShard080OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 80 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080OddDotSoundness i
          suzukiDF6D4FixedGridShard080OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 80 k) := by
    simpa [suzukiDF6D4FixedGridShard080OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard080OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 80 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 80) := by
    rw [suzukiDF6D4FixedGridShard080OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 80)
  rw [suzukiDF6D4FixedGridShard080OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard080OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard080OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard080OddDotSoundness i
            suzukiDF6D4FixedGridShard080OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard080OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard080EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard080EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 381) := by
  have h := suzukiDF6D4FixedGridShard080Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard080EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 381)) at h
  exact h

theorem suzukiDF6D4FixedGridShard080EvenFull_eq_live :
    suzukiDF6D4FixedGridShard080EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 381) := by
  have h := suzukiDF6D4FixedGridShard080Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard080EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 381)) at h
  exact h

def suzukiDF6D4FixedGridShard080EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard080EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard080EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard080EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard080EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard080EvenResidualData =
      suzukiDF6D4FixedGridShard080EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard080Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard080EvenResidualData =
    suzukiDF6D4FixedGridShard080EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard080EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard080EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 381 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 381) := by
    rw [suzukiDF6D4FixedGridShard080EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 381
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080EvenDotSoundness i
          suzukiDF6D4FixedGridShard080EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 381) := by
    simpa [suzukiDF6D4FixedGridShard080EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard080EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 381) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 381) := by
    rw [suzukiDF6D4FixedGridShard080EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 381
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard080EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard080EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard080EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard080EvenDotSoundness i
            suzukiDF6D4FixedGridShard080EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard080EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard080OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard080OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 381) := by
  have h := suzukiDF6D4FixedGridShard080Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard080OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 381)) at h
  exact h

theorem suzukiDF6D4FixedGridShard080OddFull_eq_live :
    suzukiDF6D4FixedGridShard080OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 381) := by
  have h := suzukiDF6D4FixedGridShard080Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard080OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 381)) at h
  exact h

def suzukiDF6D4FixedGridShard080OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard080OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard080OddDotSoundness i.val
        suzukiDF6D4FixedGridShard080OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard080OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard080OddResidualData =
      suzukiDF6D4FixedGridShard080OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard080Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard080OddResidualData =
    suzukiDF6D4FixedGridShard080OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard080OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard080OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 381 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 381) := by
    rw [suzukiDF6D4FixedGridShard080OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 381
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080OddDotSoundness i
          suzukiDF6D4FixedGridShard080OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 381) := by
    simpa [suzukiDF6D4FixedGridShard080OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard080OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 381) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard080OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 381) := by
    rw [suzukiDF6D4FixedGridShard080OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 381
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard080OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard080OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard080OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard080OddDotSoundness i
            suzukiDF6D4FixedGridShard080OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard080OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
