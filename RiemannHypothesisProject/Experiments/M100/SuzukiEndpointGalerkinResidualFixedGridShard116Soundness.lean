import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard116Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard116Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard116EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard116EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 116 k) := by
  have h := suzukiDF6D4FixedGridShard116Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard116EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 116 k)) at h
  exact h

def suzukiDF6D4FixedGridShard116EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard116EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard116EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard116EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard116EvenComparisonData)

theorem suzukiDF6D4FixedGridShard116EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard116EvenSolveData =
      suzukiDF6D4FixedGridShard116EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard116Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard116EvenSolveData =
    suzukiDF6D4FixedGridShard116EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard116EvenCross_eq_live :
    suzukiDF6D4FixedGridShard116EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 116) := by
  have h := suzukiDF6D4FixedGridShard116Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard116EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 116)) at h
  exact h

theorem suzukiDF6D4FixedGridShard116EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard116EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 116 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 116 k) := by
    rw [suzukiDF6D4FixedGridShard116EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 116 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116EvenDotSoundness i
          suzukiDF6D4FixedGridShard116EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 116 k) := by
    simpa [suzukiDF6D4FixedGridShard116EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard116EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 116 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 116) := by
    rw [suzukiDF6D4FixedGridShard116EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 116)
  rw [suzukiDF6D4FixedGridShard116EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard116EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard116EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard116EvenDotSoundness i
            suzukiDF6D4FixedGridShard116EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard116EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard116OddComparison_eq_live :
    suzukiDF6D4FixedGridShard116OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 116 k) := by
  have h := suzukiDF6D4FixedGridShard116Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard116OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 116 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard116OddCross_eq_live :
    suzukiDF6D4FixedGridShard116OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 116) := by
  have h := suzukiDF6D4FixedGridShard116Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard116OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 116)) at h
  exact h

def suzukiDF6D4FixedGridShard116OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard116OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard116OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard116OddDotSoundness i.val
      suzukiDF6D4FixedGridShard116OddComparisonData)

theorem suzukiDF6D4FixedGridShard116OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard116OddSolveData =
      suzukiDF6D4FixedGridShard116OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard116Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard116OddSolveData =
    suzukiDF6D4FixedGridShard116OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard116OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard116OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 116 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 116 k) := by
    rw [suzukiDF6D4FixedGridShard116OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 116 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116OddDotSoundness i
          suzukiDF6D4FixedGridShard116OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 116 k) := by
    simpa [suzukiDF6D4FixedGridShard116OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard116OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 116 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 116) := by
    rw [suzukiDF6D4FixedGridShard116OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 116)
  rw [suzukiDF6D4FixedGridShard116OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard116OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard116OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard116OddDotSoundness i
            suzukiDF6D4FixedGridShard116OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard116OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard116EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard116EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 417) := by
  have h := suzukiDF6D4FixedGridShard116Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard116EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 417)) at h
  exact h

theorem suzukiDF6D4FixedGridShard116EvenFull_eq_live :
    suzukiDF6D4FixedGridShard116EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 417) := by
  have h := suzukiDF6D4FixedGridShard116Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard116EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 417)) at h
  exact h

def suzukiDF6D4FixedGridShard116EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard116EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard116EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard116EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard116EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard116EvenResidualData =
      suzukiDF6D4FixedGridShard116EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard116Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard116EvenResidualData =
    suzukiDF6D4FixedGridShard116EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard116EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard116EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 417 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 417) := by
    rw [suzukiDF6D4FixedGridShard116EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 417
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116EvenDotSoundness i
          suzukiDF6D4FixedGridShard116EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 417) := by
    simpa [suzukiDF6D4FixedGridShard116EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard116EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 417) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 417) := by
    rw [suzukiDF6D4FixedGridShard116EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 417
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard116EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard116EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard116EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard116EvenDotSoundness i
            suzukiDF6D4FixedGridShard116EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard116EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard116OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard116OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 417) := by
  have h := suzukiDF6D4FixedGridShard116Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard116OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 417)) at h
  exact h

theorem suzukiDF6D4FixedGridShard116OddFull_eq_live :
    suzukiDF6D4FixedGridShard116OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 417) := by
  have h := suzukiDF6D4FixedGridShard116Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard116OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 417)) at h
  exact h

def suzukiDF6D4FixedGridShard116OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard116OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard116OddDotSoundness i.val
        suzukiDF6D4FixedGridShard116OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard116OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard116OddResidualData =
      suzukiDF6D4FixedGridShard116OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard116Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard116OddResidualData =
    suzukiDF6D4FixedGridShard116OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard116OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard116OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 417 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 417) := by
    rw [suzukiDF6D4FixedGridShard116OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 417
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116OddDotSoundness i
          suzukiDF6D4FixedGridShard116OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 417) := by
    simpa [suzukiDF6D4FixedGridShard116OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard116OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 417) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard116OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 417) := by
    rw [suzukiDF6D4FixedGridShard116OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 417
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard116OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard116OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard116OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard116OddDotSoundness i
            suzukiDF6D4FixedGridShard116OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard116OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
