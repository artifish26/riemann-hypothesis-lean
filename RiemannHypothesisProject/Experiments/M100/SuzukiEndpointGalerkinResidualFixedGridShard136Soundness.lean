import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard136Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard136Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard136EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard136EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 136 k) := by
  have h := suzukiDF6D4FixedGridShard136Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard136EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 136 k)) at h
  exact h

def suzukiDF6D4FixedGridShard136EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard136EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard136EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard136EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard136EvenComparisonData)

theorem suzukiDF6D4FixedGridShard136EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard136EvenSolveData =
      suzukiDF6D4FixedGridShard136EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard136Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard136EvenSolveData =
    suzukiDF6D4FixedGridShard136EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard136EvenCross_eq_live :
    suzukiDF6D4FixedGridShard136EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 136) := by
  have h := suzukiDF6D4FixedGridShard136Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard136EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 136)) at h
  exact h

theorem suzukiDF6D4FixedGridShard136EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard136EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 136 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 136 k) := by
    rw [suzukiDF6D4FixedGridShard136EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 136 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136EvenDotSoundness i
          suzukiDF6D4FixedGridShard136EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 136 k) := by
    simpa [suzukiDF6D4FixedGridShard136EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard136EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 136 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 136) := by
    rw [suzukiDF6D4FixedGridShard136EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 136)
  rw [suzukiDF6D4FixedGridShard136EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard136EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard136EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard136EvenDotSoundness i
            suzukiDF6D4FixedGridShard136EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard136EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard136OddComparison_eq_live :
    suzukiDF6D4FixedGridShard136OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 136 k) := by
  have h := suzukiDF6D4FixedGridShard136Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard136OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 136 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard136OddCross_eq_live :
    suzukiDF6D4FixedGridShard136OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 136) := by
  have h := suzukiDF6D4FixedGridShard136Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard136OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 136)) at h
  exact h

def suzukiDF6D4FixedGridShard136OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard136OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard136OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard136OddDotSoundness i.val
      suzukiDF6D4FixedGridShard136OddComparisonData)

theorem suzukiDF6D4FixedGridShard136OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard136OddSolveData =
      suzukiDF6D4FixedGridShard136OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard136Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard136OddSolveData =
    suzukiDF6D4FixedGridShard136OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard136OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard136OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 136 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 136 k) := by
    rw [suzukiDF6D4FixedGridShard136OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 136 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136OddDotSoundness i
          suzukiDF6D4FixedGridShard136OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 136 k) := by
    simpa [suzukiDF6D4FixedGridShard136OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard136OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 136 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 136) := by
    rw [suzukiDF6D4FixedGridShard136OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 136)
  rw [suzukiDF6D4FixedGridShard136OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard136OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard136OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard136OddDotSoundness i
            suzukiDF6D4FixedGridShard136OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard136OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard136EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard136EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 437) := by
  have h := suzukiDF6D4FixedGridShard136Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard136EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 437)) at h
  exact h

theorem suzukiDF6D4FixedGridShard136EvenFull_eq_live :
    suzukiDF6D4FixedGridShard136EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 437) := by
  have h := suzukiDF6D4FixedGridShard136Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard136EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 437)) at h
  exact h

def suzukiDF6D4FixedGridShard136EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard136EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard136EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard136EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard136EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard136EvenResidualData =
      suzukiDF6D4FixedGridShard136EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard136Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard136EvenResidualData =
    suzukiDF6D4FixedGridShard136EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard136EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard136EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 437 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 437) := by
    rw [suzukiDF6D4FixedGridShard136EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 437
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136EvenDotSoundness i
          suzukiDF6D4FixedGridShard136EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 437) := by
    simpa [suzukiDF6D4FixedGridShard136EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard136EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 437) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 437) := by
    rw [suzukiDF6D4FixedGridShard136EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 437
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard136EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard136EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard136EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard136EvenDotSoundness i
            suzukiDF6D4FixedGridShard136EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard136EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard136OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard136OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 437) := by
  have h := suzukiDF6D4FixedGridShard136Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard136OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 437)) at h
  exact h

theorem suzukiDF6D4FixedGridShard136OddFull_eq_live :
    suzukiDF6D4FixedGridShard136OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 437) := by
  have h := suzukiDF6D4FixedGridShard136Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard136OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 437)) at h
  exact h

def suzukiDF6D4FixedGridShard136OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard136OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard136OddDotSoundness i.val
        suzukiDF6D4FixedGridShard136OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard136OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard136OddResidualData =
      suzukiDF6D4FixedGridShard136OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard136Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard136OddResidualData =
    suzukiDF6D4FixedGridShard136OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard136OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard136OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 437 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 437) := by
    rw [suzukiDF6D4FixedGridShard136OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 437
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136OddDotSoundness i
          suzukiDF6D4FixedGridShard136OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 437) := by
    simpa [suzukiDF6D4FixedGridShard136OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard136OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 437) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard136OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 437) := by
    rw [suzukiDF6D4FixedGridShard136OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 437
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard136OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard136OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard136OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard136OddDotSoundness i
            suzukiDF6D4FixedGridShard136OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard136OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
