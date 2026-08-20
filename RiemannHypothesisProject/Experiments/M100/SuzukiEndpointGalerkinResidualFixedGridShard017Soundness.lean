import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard017Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard017Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard017EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard017EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 17 k) := by
  have h := suzukiDF6D4FixedGridShard017Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard017EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 17 k)) at h
  exact h

def suzukiDF6D4FixedGridShard017EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard017EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard017EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard017EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard017EvenComparisonData)

theorem suzukiDF6D4FixedGridShard017EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard017EvenSolveData =
      suzukiDF6D4FixedGridShard017EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard017Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard017EvenSolveData =
    suzukiDF6D4FixedGridShard017EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard017EvenCross_eq_live :
    suzukiDF6D4FixedGridShard017EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 17) := by
  have h := suzukiDF6D4FixedGridShard017Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard017EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 17)) at h
  exact h

theorem suzukiDF6D4FixedGridShard017EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard017EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 17 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 17 k) := by
    rw [suzukiDF6D4FixedGridShard017EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 17 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017EvenDotSoundness i
          suzukiDF6D4FixedGridShard017EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 17 k) := by
    simpa [suzukiDF6D4FixedGridShard017EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard017EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 17 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 17) := by
    rw [suzukiDF6D4FixedGridShard017EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 17)
  rw [suzukiDF6D4FixedGridShard017EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard017EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard017EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard017EvenDotSoundness i
            suzukiDF6D4FixedGridShard017EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard017EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard017OddComparison_eq_live :
    suzukiDF6D4FixedGridShard017OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 17 k) := by
  have h := suzukiDF6D4FixedGridShard017Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard017OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 17 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard017OddCross_eq_live :
    suzukiDF6D4FixedGridShard017OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 17) := by
  have h := suzukiDF6D4FixedGridShard017Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard017OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 17)) at h
  exact h

def suzukiDF6D4FixedGridShard017OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard017OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard017OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard017OddDotSoundness i.val
      suzukiDF6D4FixedGridShard017OddComparisonData)

theorem suzukiDF6D4FixedGridShard017OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard017OddSolveData =
      suzukiDF6D4FixedGridShard017OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard017Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard017OddSolveData =
    suzukiDF6D4FixedGridShard017OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard017OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard017OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 17 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 17 k) := by
    rw [suzukiDF6D4FixedGridShard017OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 17 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017OddDotSoundness i
          suzukiDF6D4FixedGridShard017OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 17 k) := by
    simpa [suzukiDF6D4FixedGridShard017OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard017OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 17 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 17) := by
    rw [suzukiDF6D4FixedGridShard017OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 17)
  rw [suzukiDF6D4FixedGridShard017OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard017OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard017OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard017OddDotSoundness i
            suzukiDF6D4FixedGridShard017OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard017OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard017EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard017EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 318) := by
  have h := suzukiDF6D4FixedGridShard017Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard017EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 318)) at h
  exact h

theorem suzukiDF6D4FixedGridShard017EvenFull_eq_live :
    suzukiDF6D4FixedGridShard017EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 318) := by
  have h := suzukiDF6D4FixedGridShard017Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard017EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 318)) at h
  exact h

def suzukiDF6D4FixedGridShard017EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard017EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard017EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard017EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard017EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard017EvenResidualData =
      suzukiDF6D4FixedGridShard017EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard017Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard017EvenResidualData =
    suzukiDF6D4FixedGridShard017EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard017EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard017EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 318 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 318) := by
    rw [suzukiDF6D4FixedGridShard017EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 318
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017EvenDotSoundness i
          suzukiDF6D4FixedGridShard017EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 318) := by
    simpa [suzukiDF6D4FixedGridShard017EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard017EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 318) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 318) := by
    rw [suzukiDF6D4FixedGridShard017EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 318
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard017EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard017EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard017EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard017EvenDotSoundness i
            suzukiDF6D4FixedGridShard017EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard017EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard017OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard017OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 318) := by
  have h := suzukiDF6D4FixedGridShard017Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard017OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 318)) at h
  exact h

theorem suzukiDF6D4FixedGridShard017OddFull_eq_live :
    suzukiDF6D4FixedGridShard017OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 318) := by
  have h := suzukiDF6D4FixedGridShard017Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard017OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 318)) at h
  exact h

def suzukiDF6D4FixedGridShard017OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard017OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard017OddDotSoundness i.val
        suzukiDF6D4FixedGridShard017OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard017OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard017OddResidualData =
      suzukiDF6D4FixedGridShard017OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard017Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard017OddResidualData =
    suzukiDF6D4FixedGridShard017OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard017OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard017OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 318 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 318) := by
    rw [suzukiDF6D4FixedGridShard017OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 318
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017OddDotSoundness i
          suzukiDF6D4FixedGridShard017OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 318) := by
    simpa [suzukiDF6D4FixedGridShard017OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard017OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 318) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard017OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 318) := by
    rw [suzukiDF6D4FixedGridShard017OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 318
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard017OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard017OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard017OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard017OddDotSoundness i
            suzukiDF6D4FixedGridShard017OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard017OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
