import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard152Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard152Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard152EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard152EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 152 k) := by
  have h := suzukiDF6D4FixedGridShard152Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard152EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 152 k)) at h
  exact h

def suzukiDF6D4FixedGridShard152EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard152EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard152EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard152EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard152EvenComparisonData)

theorem suzukiDF6D4FixedGridShard152EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard152EvenSolveData =
      suzukiDF6D4FixedGridShard152EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard152Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard152EvenSolveData =
    suzukiDF6D4FixedGridShard152EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard152EvenCross_eq_live :
    suzukiDF6D4FixedGridShard152EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 152) := by
  have h := suzukiDF6D4FixedGridShard152Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard152EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 152)) at h
  exact h

theorem suzukiDF6D4FixedGridShard152EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard152EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 152 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 152 k) := by
    rw [suzukiDF6D4FixedGridShard152EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 152 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152EvenDotSoundness i
          suzukiDF6D4FixedGridShard152EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 152 k) := by
    simpa [suzukiDF6D4FixedGridShard152EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard152EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 152 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 152) := by
    rw [suzukiDF6D4FixedGridShard152EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 152)
  rw [suzukiDF6D4FixedGridShard152EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard152EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard152EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard152EvenDotSoundness i
            suzukiDF6D4FixedGridShard152EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard152EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard152OddComparison_eq_live :
    suzukiDF6D4FixedGridShard152OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 152 k) := by
  have h := suzukiDF6D4FixedGridShard152Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard152OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 152 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard152OddCross_eq_live :
    suzukiDF6D4FixedGridShard152OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 152) := by
  have h := suzukiDF6D4FixedGridShard152Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard152OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 152)) at h
  exact h

def suzukiDF6D4FixedGridShard152OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard152OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard152OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard152OddDotSoundness i.val
      suzukiDF6D4FixedGridShard152OddComparisonData)

theorem suzukiDF6D4FixedGridShard152OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard152OddSolveData =
      suzukiDF6D4FixedGridShard152OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard152Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard152OddSolveData =
    suzukiDF6D4FixedGridShard152OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard152OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard152OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 152 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 152 k) := by
    rw [suzukiDF6D4FixedGridShard152OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 152 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152OddDotSoundness i
          suzukiDF6D4FixedGridShard152OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 152 k) := by
    simpa [suzukiDF6D4FixedGridShard152OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard152OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 152 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 152) := by
    rw [suzukiDF6D4FixedGridShard152OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 152)
  rw [suzukiDF6D4FixedGridShard152OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard152OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard152OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard152OddDotSoundness i
            suzukiDF6D4FixedGridShard152OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard152OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard152EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard152EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 453) := by
  have h := suzukiDF6D4FixedGridShard152Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard152EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 453)) at h
  exact h

theorem suzukiDF6D4FixedGridShard152EvenFull_eq_live :
    suzukiDF6D4FixedGridShard152EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 453) := by
  have h := suzukiDF6D4FixedGridShard152Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard152EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 453)) at h
  exact h

def suzukiDF6D4FixedGridShard152EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard152EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard152EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard152EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard152EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard152EvenResidualData =
      suzukiDF6D4FixedGridShard152EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard152Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard152EvenResidualData =
    suzukiDF6D4FixedGridShard152EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard152EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard152EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 453 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 453) := by
    rw [suzukiDF6D4FixedGridShard152EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 453
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152EvenDotSoundness i
          suzukiDF6D4FixedGridShard152EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 453) := by
    simpa [suzukiDF6D4FixedGridShard152EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard152EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 453) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 453) := by
    rw [suzukiDF6D4FixedGridShard152EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 453
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard152EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard152EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard152EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard152EvenDotSoundness i
            suzukiDF6D4FixedGridShard152EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard152EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard152OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard152OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 453) := by
  have h := suzukiDF6D4FixedGridShard152Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard152OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 453)) at h
  exact h

theorem suzukiDF6D4FixedGridShard152OddFull_eq_live :
    suzukiDF6D4FixedGridShard152OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 453) := by
  have h := suzukiDF6D4FixedGridShard152Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard152OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 453)) at h
  exact h

def suzukiDF6D4FixedGridShard152OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard152OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard152OddDotSoundness i.val
        suzukiDF6D4FixedGridShard152OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard152OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard152OddResidualData =
      suzukiDF6D4FixedGridShard152OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard152Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard152OddResidualData =
    suzukiDF6D4FixedGridShard152OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard152OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard152OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 453 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 453) := by
    rw [suzukiDF6D4FixedGridShard152OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 453
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152OddDotSoundness i
          suzukiDF6D4FixedGridShard152OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 453) := by
    simpa [suzukiDF6D4FixedGridShard152OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard152OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 453) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard152OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 453) := by
    rw [suzukiDF6D4FixedGridShard152OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 453
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard152OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard152OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard152OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard152OddDotSoundness i
            suzukiDF6D4FixedGridShard152OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard152OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
