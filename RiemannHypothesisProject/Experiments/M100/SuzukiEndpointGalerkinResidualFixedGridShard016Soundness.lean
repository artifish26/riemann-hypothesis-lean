import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard016Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard016Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard016EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard016EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 16 k) := by
  have h := suzukiDF6D4FixedGridShard016Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard016EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 16 k)) at h
  exact h

def suzukiDF6D4FixedGridShard016EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard016EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard016EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard016EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard016EvenComparisonData)

theorem suzukiDF6D4FixedGridShard016EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard016EvenSolveData =
      suzukiDF6D4FixedGridShard016EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard016Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard016EvenSolveData =
    suzukiDF6D4FixedGridShard016EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard016EvenCross_eq_live :
    suzukiDF6D4FixedGridShard016EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 16) := by
  have h := suzukiDF6D4FixedGridShard016Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard016EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 16)) at h
  exact h

theorem suzukiDF6D4FixedGridShard016EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard016EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 16 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 16 k) := by
    rw [suzukiDF6D4FixedGridShard016EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 16 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016EvenDotSoundness i
          suzukiDF6D4FixedGridShard016EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 16 k) := by
    simpa [suzukiDF6D4FixedGridShard016EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard016EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 16 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 16) := by
    rw [suzukiDF6D4FixedGridShard016EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 16)
  rw [suzukiDF6D4FixedGridShard016EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard016EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard016EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard016EvenDotSoundness i
            suzukiDF6D4FixedGridShard016EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard016EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard016OddComparison_eq_live :
    suzukiDF6D4FixedGridShard016OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 16 k) := by
  have h := suzukiDF6D4FixedGridShard016Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard016OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 16 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard016OddCross_eq_live :
    suzukiDF6D4FixedGridShard016OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 16) := by
  have h := suzukiDF6D4FixedGridShard016Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard016OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 16)) at h
  exact h

def suzukiDF6D4FixedGridShard016OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard016OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard016OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard016OddDotSoundness i.val
      suzukiDF6D4FixedGridShard016OddComparisonData)

theorem suzukiDF6D4FixedGridShard016OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard016OddSolveData =
      suzukiDF6D4FixedGridShard016OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard016Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard016OddSolveData =
    suzukiDF6D4FixedGridShard016OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard016OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard016OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 16 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 16 k) := by
    rw [suzukiDF6D4FixedGridShard016OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 16 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016OddDotSoundness i
          suzukiDF6D4FixedGridShard016OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 16 k) := by
    simpa [suzukiDF6D4FixedGridShard016OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard016OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 16 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 16) := by
    rw [suzukiDF6D4FixedGridShard016OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 16)
  rw [suzukiDF6D4FixedGridShard016OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard016OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard016OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard016OddDotSoundness i
            suzukiDF6D4FixedGridShard016OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard016OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard016EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard016EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 317) := by
  have h := suzukiDF6D4FixedGridShard016Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard016EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 317)) at h
  exact h

theorem suzukiDF6D4FixedGridShard016EvenFull_eq_live :
    suzukiDF6D4FixedGridShard016EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 317) := by
  have h := suzukiDF6D4FixedGridShard016Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard016EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 317)) at h
  exact h

def suzukiDF6D4FixedGridShard016EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard016EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard016EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard016EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard016EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard016EvenResidualData =
      suzukiDF6D4FixedGridShard016EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard016Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard016EvenResidualData =
    suzukiDF6D4FixedGridShard016EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard016EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard016EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 317 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 317) := by
    rw [suzukiDF6D4FixedGridShard016EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 317
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016EvenDotSoundness i
          suzukiDF6D4FixedGridShard016EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 317) := by
    simpa [suzukiDF6D4FixedGridShard016EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard016EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 317) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 317) := by
    rw [suzukiDF6D4FixedGridShard016EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 317
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard016EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard016EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard016EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard016EvenDotSoundness i
            suzukiDF6D4FixedGridShard016EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard016EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard016OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard016OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 317) := by
  have h := suzukiDF6D4FixedGridShard016Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard016OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 317)) at h
  exact h

theorem suzukiDF6D4FixedGridShard016OddFull_eq_live :
    suzukiDF6D4FixedGridShard016OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 317) := by
  have h := suzukiDF6D4FixedGridShard016Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard016OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 317)) at h
  exact h

def suzukiDF6D4FixedGridShard016OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard016OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard016OddDotSoundness i.val
        suzukiDF6D4FixedGridShard016OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard016OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard016OddResidualData =
      suzukiDF6D4FixedGridShard016OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard016Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard016OddResidualData =
    suzukiDF6D4FixedGridShard016OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard016OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard016OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 317 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 317) := by
    rw [suzukiDF6D4FixedGridShard016OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 317
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016OddDotSoundness i
          suzukiDF6D4FixedGridShard016OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 317) := by
    simpa [suzukiDF6D4FixedGridShard016OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard016OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 317) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard016OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 317) := by
    rw [suzukiDF6D4FixedGridShard016OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 317
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard016OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard016OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard016OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard016OddDotSoundness i
            suzukiDF6D4FixedGridShard016OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard016OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
