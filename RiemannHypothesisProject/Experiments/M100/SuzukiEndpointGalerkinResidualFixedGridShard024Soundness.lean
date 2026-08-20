import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard024Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard024Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard024EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard024EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 24 k) := by
  have h := suzukiDF6D4FixedGridShard024Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard024EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 24 k)) at h
  exact h

def suzukiDF6D4FixedGridShard024EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard024EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard024EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard024EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard024EvenComparisonData)

theorem suzukiDF6D4FixedGridShard024EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard024EvenSolveData =
      suzukiDF6D4FixedGridShard024EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard024Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard024EvenSolveData =
    suzukiDF6D4FixedGridShard024EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard024EvenCross_eq_live :
    suzukiDF6D4FixedGridShard024EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 24) := by
  have h := suzukiDF6D4FixedGridShard024Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard024EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 24)) at h
  exact h

theorem suzukiDF6D4FixedGridShard024EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard024EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 24 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 24 k) := by
    rw [suzukiDF6D4FixedGridShard024EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 24 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024EvenDotSoundness i
          suzukiDF6D4FixedGridShard024EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 24 k) := by
    simpa [suzukiDF6D4FixedGridShard024EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard024EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 24 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 24) := by
    rw [suzukiDF6D4FixedGridShard024EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 24)
  rw [suzukiDF6D4FixedGridShard024EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard024EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard024EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard024EvenDotSoundness i
            suzukiDF6D4FixedGridShard024EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard024EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard024OddComparison_eq_live :
    suzukiDF6D4FixedGridShard024OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 24 k) := by
  have h := suzukiDF6D4FixedGridShard024Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard024OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 24 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard024OddCross_eq_live :
    suzukiDF6D4FixedGridShard024OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 24) := by
  have h := suzukiDF6D4FixedGridShard024Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard024OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 24)) at h
  exact h

def suzukiDF6D4FixedGridShard024OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard024OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard024OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard024OddDotSoundness i.val
      suzukiDF6D4FixedGridShard024OddComparisonData)

theorem suzukiDF6D4FixedGridShard024OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard024OddSolveData =
      suzukiDF6D4FixedGridShard024OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard024Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard024OddSolveData =
    suzukiDF6D4FixedGridShard024OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard024OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard024OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 24 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 24 k) := by
    rw [suzukiDF6D4FixedGridShard024OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 24 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024OddDotSoundness i
          suzukiDF6D4FixedGridShard024OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 24 k) := by
    simpa [suzukiDF6D4FixedGridShard024OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard024OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 24 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 24) := by
    rw [suzukiDF6D4FixedGridShard024OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 24)
  rw [suzukiDF6D4FixedGridShard024OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard024OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard024OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard024OddDotSoundness i
            suzukiDF6D4FixedGridShard024OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard024OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard024EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard024EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 325) := by
  have h := suzukiDF6D4FixedGridShard024Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard024EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 325)) at h
  exact h

theorem suzukiDF6D4FixedGridShard024EvenFull_eq_live :
    suzukiDF6D4FixedGridShard024EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 325) := by
  have h := suzukiDF6D4FixedGridShard024Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard024EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 325)) at h
  exact h

def suzukiDF6D4FixedGridShard024EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard024EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard024EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard024EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard024EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard024EvenResidualData =
      suzukiDF6D4FixedGridShard024EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard024Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard024EvenResidualData =
    suzukiDF6D4FixedGridShard024EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard024EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard024EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 325 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 325) := by
    rw [suzukiDF6D4FixedGridShard024EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 325
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024EvenDotSoundness i
          suzukiDF6D4FixedGridShard024EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 325) := by
    simpa [suzukiDF6D4FixedGridShard024EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard024EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 325) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 325) := by
    rw [suzukiDF6D4FixedGridShard024EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 325
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard024EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard024EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard024EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard024EvenDotSoundness i
            suzukiDF6D4FixedGridShard024EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard024EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard024OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard024OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 325) := by
  have h := suzukiDF6D4FixedGridShard024Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard024OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 325)) at h
  exact h

theorem suzukiDF6D4FixedGridShard024OddFull_eq_live :
    suzukiDF6D4FixedGridShard024OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 325) := by
  have h := suzukiDF6D4FixedGridShard024Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard024OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 325)) at h
  exact h

def suzukiDF6D4FixedGridShard024OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard024OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard024OddDotSoundness i.val
        suzukiDF6D4FixedGridShard024OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard024OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard024OddResidualData =
      suzukiDF6D4FixedGridShard024OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard024Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard024OddResidualData =
    suzukiDF6D4FixedGridShard024OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard024OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard024OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 325 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 325) := by
    rw [suzukiDF6D4FixedGridShard024OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 325
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024OddDotSoundness i
          suzukiDF6D4FixedGridShard024OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 325) := by
    simpa [suzukiDF6D4FixedGridShard024OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard024OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 325) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard024OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 325) := by
    rw [suzukiDF6D4FixedGridShard024OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 325
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard024OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard024OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard024OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard024OddDotSoundness i
            suzukiDF6D4FixedGridShard024OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard024OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
