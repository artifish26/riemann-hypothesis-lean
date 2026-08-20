import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard189Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard189Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard189EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard189EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 189 k) := by
  have h := suzukiDF6D4FixedGridShard189Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard189EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 189 k)) at h
  exact h

def suzukiDF6D4FixedGridShard189EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard189EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard189EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard189EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard189EvenComparisonData)

theorem suzukiDF6D4FixedGridShard189EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard189EvenSolveData =
      suzukiDF6D4FixedGridShard189EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard189Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard189EvenSolveData =
    suzukiDF6D4FixedGridShard189EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard189EvenCross_eq_live :
    suzukiDF6D4FixedGridShard189EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 189) := by
  have h := suzukiDF6D4FixedGridShard189Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard189EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 189)) at h
  exact h

theorem suzukiDF6D4FixedGridShard189EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard189EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 189 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 189 k) := by
    rw [suzukiDF6D4FixedGridShard189EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 189 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189EvenDotSoundness i
          suzukiDF6D4FixedGridShard189EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 189 k) := by
    simpa [suzukiDF6D4FixedGridShard189EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard189EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 189 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 189) := by
    rw [suzukiDF6D4FixedGridShard189EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 189)
  rw [suzukiDF6D4FixedGridShard189EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard189EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard189EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard189EvenDotSoundness i
            suzukiDF6D4FixedGridShard189EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard189EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard189OddComparison_eq_live :
    suzukiDF6D4FixedGridShard189OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 189 k) := by
  have h := suzukiDF6D4FixedGridShard189Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard189OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 189 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard189OddCross_eq_live :
    suzukiDF6D4FixedGridShard189OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 189) := by
  have h := suzukiDF6D4FixedGridShard189Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard189OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 189)) at h
  exact h

def suzukiDF6D4FixedGridShard189OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard189OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard189OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard189OddDotSoundness i.val
      suzukiDF6D4FixedGridShard189OddComparisonData)

theorem suzukiDF6D4FixedGridShard189OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard189OddSolveData =
      suzukiDF6D4FixedGridShard189OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard189Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard189OddSolveData =
    suzukiDF6D4FixedGridShard189OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard189OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard189OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 189 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 189 k) := by
    rw [suzukiDF6D4FixedGridShard189OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 189 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189OddDotSoundness i
          suzukiDF6D4FixedGridShard189OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 189 k) := by
    simpa [suzukiDF6D4FixedGridShard189OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard189OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 189 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 189) := by
    rw [suzukiDF6D4FixedGridShard189OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 189)
  rw [suzukiDF6D4FixedGridShard189OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard189OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard189OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard189OddDotSoundness i
            suzukiDF6D4FixedGridShard189OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard189OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard189EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard189EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 490) := by
  have h := suzukiDF6D4FixedGridShard189Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard189EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 490)) at h
  exact h

theorem suzukiDF6D4FixedGridShard189EvenFull_eq_live :
    suzukiDF6D4FixedGridShard189EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 490) := by
  have h := suzukiDF6D4FixedGridShard189Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard189EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 490)) at h
  exact h

def suzukiDF6D4FixedGridShard189EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard189EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard189EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard189EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard189EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard189EvenResidualData =
      suzukiDF6D4FixedGridShard189EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard189Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard189EvenResidualData =
    suzukiDF6D4FixedGridShard189EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard189EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard189EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 490 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 490) := by
    rw [suzukiDF6D4FixedGridShard189EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 490
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189EvenDotSoundness i
          suzukiDF6D4FixedGridShard189EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 490) := by
    simpa [suzukiDF6D4FixedGridShard189EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard189EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 490) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 490) := by
    rw [suzukiDF6D4FixedGridShard189EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 490
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard189EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard189EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard189EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard189EvenDotSoundness i
            suzukiDF6D4FixedGridShard189EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard189EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard189OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard189OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 490) := by
  have h := suzukiDF6D4FixedGridShard189Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard189OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 490)) at h
  exact h

theorem suzukiDF6D4FixedGridShard189OddFull_eq_live :
    suzukiDF6D4FixedGridShard189OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 490) := by
  have h := suzukiDF6D4FixedGridShard189Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard189OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 490)) at h
  exact h

def suzukiDF6D4FixedGridShard189OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard189OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard189OddDotSoundness i.val
        suzukiDF6D4FixedGridShard189OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard189OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard189OddResidualData =
      suzukiDF6D4FixedGridShard189OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard189Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard189OddResidualData =
    suzukiDF6D4FixedGridShard189OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard189OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard189OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 490 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 490) := by
    rw [suzukiDF6D4FixedGridShard189OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 490
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189OddDotSoundness i
          suzukiDF6D4FixedGridShard189OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 490) := by
    simpa [suzukiDF6D4FixedGridShard189OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard189OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 490) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard189OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 490) := by
    rw [suzukiDF6D4FixedGridShard189OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 490
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard189OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard189OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard189OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard189OddDotSoundness i
            suzukiDF6D4FixedGridShard189OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard189OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
