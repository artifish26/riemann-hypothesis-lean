import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard192Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard192Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard192EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard192EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 192 k) := by
  have h := suzukiDF6D4FixedGridShard192Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard192EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 192 k)) at h
  exact h

def suzukiDF6D4FixedGridShard192EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard192EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard192EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard192EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard192EvenComparisonData)

theorem suzukiDF6D4FixedGridShard192EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard192EvenSolveData =
      suzukiDF6D4FixedGridShard192EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard192Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard192EvenSolveData =
    suzukiDF6D4FixedGridShard192EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard192EvenCross_eq_live :
    suzukiDF6D4FixedGridShard192EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 192) := by
  have h := suzukiDF6D4FixedGridShard192Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard192EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 192)) at h
  exact h

theorem suzukiDF6D4FixedGridShard192EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard192EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 192 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 192 k) := by
    rw [suzukiDF6D4FixedGridShard192EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 192 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192EvenDotSoundness i
          suzukiDF6D4FixedGridShard192EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 192 k) := by
    simpa [suzukiDF6D4FixedGridShard192EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard192EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 192 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 192) := by
    rw [suzukiDF6D4FixedGridShard192EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 192)
  rw [suzukiDF6D4FixedGridShard192EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard192EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard192EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard192EvenDotSoundness i
            suzukiDF6D4FixedGridShard192EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard192EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard192OddComparison_eq_live :
    suzukiDF6D4FixedGridShard192OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 192 k) := by
  have h := suzukiDF6D4FixedGridShard192Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard192OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 192 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard192OddCross_eq_live :
    suzukiDF6D4FixedGridShard192OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 192) := by
  have h := suzukiDF6D4FixedGridShard192Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard192OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 192)) at h
  exact h

def suzukiDF6D4FixedGridShard192OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard192OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard192OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard192OddDotSoundness i.val
      suzukiDF6D4FixedGridShard192OddComparisonData)

theorem suzukiDF6D4FixedGridShard192OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard192OddSolveData =
      suzukiDF6D4FixedGridShard192OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard192Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard192OddSolveData =
    suzukiDF6D4FixedGridShard192OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard192OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard192OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 192 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 192 k) := by
    rw [suzukiDF6D4FixedGridShard192OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 192 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192OddDotSoundness i
          suzukiDF6D4FixedGridShard192OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 192 k) := by
    simpa [suzukiDF6D4FixedGridShard192OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard192OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 192 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 192) := by
    rw [suzukiDF6D4FixedGridShard192OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 192)
  rw [suzukiDF6D4FixedGridShard192OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard192OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard192OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard192OddDotSoundness i
            suzukiDF6D4FixedGridShard192OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard192OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard192EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard192EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 493) := by
  have h := suzukiDF6D4FixedGridShard192Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard192EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 493)) at h
  exact h

theorem suzukiDF6D4FixedGridShard192EvenFull_eq_live :
    suzukiDF6D4FixedGridShard192EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 493) := by
  have h := suzukiDF6D4FixedGridShard192Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard192EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 493)) at h
  exact h

def suzukiDF6D4FixedGridShard192EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard192EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard192EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard192EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard192EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard192EvenResidualData =
      suzukiDF6D4FixedGridShard192EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard192Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard192EvenResidualData =
    suzukiDF6D4FixedGridShard192EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard192EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard192EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 493 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 493) := by
    rw [suzukiDF6D4FixedGridShard192EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 493
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192EvenDotSoundness i
          suzukiDF6D4FixedGridShard192EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 493) := by
    simpa [suzukiDF6D4FixedGridShard192EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard192EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 493) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 493) := by
    rw [suzukiDF6D4FixedGridShard192EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 493
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard192EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard192EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard192EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard192EvenDotSoundness i
            suzukiDF6D4FixedGridShard192EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard192EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard192OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard192OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 493) := by
  have h := suzukiDF6D4FixedGridShard192Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard192OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 493)) at h
  exact h

theorem suzukiDF6D4FixedGridShard192OddFull_eq_live :
    suzukiDF6D4FixedGridShard192OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 493) := by
  have h := suzukiDF6D4FixedGridShard192Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard192OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 493)) at h
  exact h

def suzukiDF6D4FixedGridShard192OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard192OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard192OddDotSoundness i.val
        suzukiDF6D4FixedGridShard192OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard192OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard192OddResidualData =
      suzukiDF6D4FixedGridShard192OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard192Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard192OddResidualData =
    suzukiDF6D4FixedGridShard192OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard192OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard192OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 493 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 493) := by
    rw [suzukiDF6D4FixedGridShard192OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 493
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192OddDotSoundness i
          suzukiDF6D4FixedGridShard192OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 493) := by
    simpa [suzukiDF6D4FixedGridShard192OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard192OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 493) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard192OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 493) := by
    rw [suzukiDF6D4FixedGridShard192OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 493
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard192OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard192OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard192OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard192OddDotSoundness i
            suzukiDF6D4FixedGridShard192OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard192OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
