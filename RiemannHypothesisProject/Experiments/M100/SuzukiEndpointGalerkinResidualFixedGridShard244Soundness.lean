import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard244Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard244Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard244EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard244EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 244 k) := by
  have h := suzukiDF6D4FixedGridShard244Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard244EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 244 k)) at h
  exact h

def suzukiDF6D4FixedGridShard244EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard244EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard244EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard244EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard244EvenComparisonData)

theorem suzukiDF6D4FixedGridShard244EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard244EvenSolveData =
      suzukiDF6D4FixedGridShard244EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard244Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard244EvenSolveData =
    suzukiDF6D4FixedGridShard244EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard244EvenCross_eq_live :
    suzukiDF6D4FixedGridShard244EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 244) := by
  have h := suzukiDF6D4FixedGridShard244Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard244EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 244)) at h
  exact h

theorem suzukiDF6D4FixedGridShard244EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard244EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 244 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 244 k) := by
    rw [suzukiDF6D4FixedGridShard244EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 244 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244EvenDotSoundness i
          suzukiDF6D4FixedGridShard244EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 244 k) := by
    simpa [suzukiDF6D4FixedGridShard244EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard244EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 244 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 244) := by
    rw [suzukiDF6D4FixedGridShard244EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 244)
  rw [suzukiDF6D4FixedGridShard244EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard244EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard244EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard244EvenDotSoundness i
            suzukiDF6D4FixedGridShard244EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard244EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard244OddComparison_eq_live :
    suzukiDF6D4FixedGridShard244OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 244 k) := by
  have h := suzukiDF6D4FixedGridShard244Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard244OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 244 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard244OddCross_eq_live :
    suzukiDF6D4FixedGridShard244OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 244) := by
  have h := suzukiDF6D4FixedGridShard244Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard244OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 244)) at h
  exact h

def suzukiDF6D4FixedGridShard244OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard244OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard244OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard244OddDotSoundness i.val
      suzukiDF6D4FixedGridShard244OddComparisonData)

theorem suzukiDF6D4FixedGridShard244OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard244OddSolveData =
      suzukiDF6D4FixedGridShard244OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard244Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard244OddSolveData =
    suzukiDF6D4FixedGridShard244OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard244OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard244OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 244 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 244 k) := by
    rw [suzukiDF6D4FixedGridShard244OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 244 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244OddDotSoundness i
          suzukiDF6D4FixedGridShard244OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 244 k) := by
    simpa [suzukiDF6D4FixedGridShard244OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard244OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 244 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 244) := by
    rw [suzukiDF6D4FixedGridShard244OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 244)
  rw [suzukiDF6D4FixedGridShard244OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard244OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard244OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard244OddDotSoundness i
            suzukiDF6D4FixedGridShard244OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard244OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard244EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard244EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 545) := by
  have h := suzukiDF6D4FixedGridShard244Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard244EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 545)) at h
  exact h

theorem suzukiDF6D4FixedGridShard244EvenFull_eq_live :
    suzukiDF6D4FixedGridShard244EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 545) := by
  have h := suzukiDF6D4FixedGridShard244Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard244EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 545)) at h
  exact h

def suzukiDF6D4FixedGridShard244EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard244EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard244EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard244EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard244EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard244EvenResidualData =
      suzukiDF6D4FixedGridShard244EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard244Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard244EvenResidualData =
    suzukiDF6D4FixedGridShard244EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard244EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard244EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 545 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 545) := by
    rw [suzukiDF6D4FixedGridShard244EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 545
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244EvenDotSoundness i
          suzukiDF6D4FixedGridShard244EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 545) := by
    simpa [suzukiDF6D4FixedGridShard244EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard244EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 545) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 545) := by
    rw [suzukiDF6D4FixedGridShard244EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 545
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard244EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard244EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard244EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard244EvenDotSoundness i
            suzukiDF6D4FixedGridShard244EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard244EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard244OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard244OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 545) := by
  have h := suzukiDF6D4FixedGridShard244Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard244OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 545)) at h
  exact h

theorem suzukiDF6D4FixedGridShard244OddFull_eq_live :
    suzukiDF6D4FixedGridShard244OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 545) := by
  have h := suzukiDF6D4FixedGridShard244Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard244OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 545)) at h
  exact h

def suzukiDF6D4FixedGridShard244OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard244OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard244OddDotSoundness i.val
        suzukiDF6D4FixedGridShard244OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard244OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard244OddResidualData =
      suzukiDF6D4FixedGridShard244OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard244Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard244OddResidualData =
    suzukiDF6D4FixedGridShard244OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard244OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard244OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 545 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 545) := by
    rw [suzukiDF6D4FixedGridShard244OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 545
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244OddDotSoundness i
          suzukiDF6D4FixedGridShard244OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 545) := by
    simpa [suzukiDF6D4FixedGridShard244OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard244OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 545) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard244OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 545) := by
    rw [suzukiDF6D4FixedGridShard244OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 545
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard244OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard244OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard244OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard244OddDotSoundness i
            suzukiDF6D4FixedGridShard244OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard244OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
