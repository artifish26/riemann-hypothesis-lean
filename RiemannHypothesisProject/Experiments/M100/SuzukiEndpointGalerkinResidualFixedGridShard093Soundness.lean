import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard093Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard093Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard093EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard093EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 93 k) := by
  have h := suzukiDF6D4FixedGridShard093Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard093EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 93 k)) at h
  exact h

def suzukiDF6D4FixedGridShard093EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard093EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard093EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard093EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard093EvenComparisonData)

theorem suzukiDF6D4FixedGridShard093EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard093EvenSolveData =
      suzukiDF6D4FixedGridShard093EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard093Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard093EvenSolveData =
    suzukiDF6D4FixedGridShard093EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard093EvenCross_eq_live :
    suzukiDF6D4FixedGridShard093EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 93) := by
  have h := suzukiDF6D4FixedGridShard093Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard093EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 93)) at h
  exact h

theorem suzukiDF6D4FixedGridShard093EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard093EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 93 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 93 k) := by
    rw [suzukiDF6D4FixedGridShard093EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 93 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093EvenDotSoundness i
          suzukiDF6D4FixedGridShard093EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 93 k) := by
    simpa [suzukiDF6D4FixedGridShard093EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard093EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 93 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 93) := by
    rw [suzukiDF6D4FixedGridShard093EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 93)
  rw [suzukiDF6D4FixedGridShard093EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard093EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard093EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard093EvenDotSoundness i
            suzukiDF6D4FixedGridShard093EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard093EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard093OddComparison_eq_live :
    suzukiDF6D4FixedGridShard093OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 93 k) := by
  have h := suzukiDF6D4FixedGridShard093Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard093OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 93 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard093OddCross_eq_live :
    suzukiDF6D4FixedGridShard093OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 93) := by
  have h := suzukiDF6D4FixedGridShard093Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard093OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 93)) at h
  exact h

def suzukiDF6D4FixedGridShard093OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard093OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard093OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard093OddDotSoundness i.val
      suzukiDF6D4FixedGridShard093OddComparisonData)

theorem suzukiDF6D4FixedGridShard093OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard093OddSolveData =
      suzukiDF6D4FixedGridShard093OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard093Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard093OddSolveData =
    suzukiDF6D4FixedGridShard093OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard093OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard093OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 93 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 93 k) := by
    rw [suzukiDF6D4FixedGridShard093OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 93 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093OddDotSoundness i
          suzukiDF6D4FixedGridShard093OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 93 k) := by
    simpa [suzukiDF6D4FixedGridShard093OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard093OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 93 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 93) := by
    rw [suzukiDF6D4FixedGridShard093OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 93)
  rw [suzukiDF6D4FixedGridShard093OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard093OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard093OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard093OddDotSoundness i
            suzukiDF6D4FixedGridShard093OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard093OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard093EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard093EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 394) := by
  have h := suzukiDF6D4FixedGridShard093Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard093EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 394)) at h
  exact h

theorem suzukiDF6D4FixedGridShard093EvenFull_eq_live :
    suzukiDF6D4FixedGridShard093EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 394) := by
  have h := suzukiDF6D4FixedGridShard093Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard093EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 394)) at h
  exact h

def suzukiDF6D4FixedGridShard093EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard093EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard093EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard093EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard093EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard093EvenResidualData =
      suzukiDF6D4FixedGridShard093EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard093Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard093EvenResidualData =
    suzukiDF6D4FixedGridShard093EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard093EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard093EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 394 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 394) := by
    rw [suzukiDF6D4FixedGridShard093EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 394
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093EvenDotSoundness i
          suzukiDF6D4FixedGridShard093EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 394) := by
    simpa [suzukiDF6D4FixedGridShard093EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard093EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 394) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 394) := by
    rw [suzukiDF6D4FixedGridShard093EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 394
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard093EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard093EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard093EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard093EvenDotSoundness i
            suzukiDF6D4FixedGridShard093EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard093EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard093OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard093OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 394) := by
  have h := suzukiDF6D4FixedGridShard093Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard093OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 394)) at h
  exact h

theorem suzukiDF6D4FixedGridShard093OddFull_eq_live :
    suzukiDF6D4FixedGridShard093OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 394) := by
  have h := suzukiDF6D4FixedGridShard093Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard093OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 394)) at h
  exact h

def suzukiDF6D4FixedGridShard093OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard093OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard093OddDotSoundness i.val
        suzukiDF6D4FixedGridShard093OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard093OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard093OddResidualData =
      suzukiDF6D4FixedGridShard093OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard093Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard093OddResidualData =
    suzukiDF6D4FixedGridShard093OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard093OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard093OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 394 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 394) := by
    rw [suzukiDF6D4FixedGridShard093OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 394
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093OddDotSoundness i
          suzukiDF6D4FixedGridShard093OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 394) := by
    simpa [suzukiDF6D4FixedGridShard093OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard093OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 394) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard093OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 394) := by
    rw [suzukiDF6D4FixedGridShard093OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 394
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard093OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard093OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard093OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard093OddDotSoundness i
            suzukiDF6D4FixedGridShard093OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard093OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
