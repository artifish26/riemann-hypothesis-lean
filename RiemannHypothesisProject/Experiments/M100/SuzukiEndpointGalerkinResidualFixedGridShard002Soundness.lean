import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard002Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard002Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard002EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard002EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 2 k) := by
  have h := suzukiDF6D4FixedGridShard002Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard002EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 2 k)) at h
  exact h

def suzukiDF6D4FixedGridShard002EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard002EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard002EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard002EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard002EvenComparisonData)

theorem suzukiDF6D4FixedGridShard002EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard002EvenSolveData =
      suzukiDF6D4FixedGridShard002EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard002Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard002EvenSolveData =
    suzukiDF6D4FixedGridShard002EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard002EvenCross_eq_live :
    suzukiDF6D4FixedGridShard002EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 2) := by
  have h := suzukiDF6D4FixedGridShard002Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard002EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 2)) at h
  exact h

theorem suzukiDF6D4FixedGridShard002EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard002EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 2 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 2 k) := by
    rw [suzukiDF6D4FixedGridShard002EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 2 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002EvenDotSoundness i
          suzukiDF6D4FixedGridShard002EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 2 k) := by
    simpa [suzukiDF6D4FixedGridShard002EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard002EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 2 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 2) := by
    rw [suzukiDF6D4FixedGridShard002EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 2)
  rw [suzukiDF6D4FixedGridShard002EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard002EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard002EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard002EvenDotSoundness i
            suzukiDF6D4FixedGridShard002EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard002EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard002OddComparison_eq_live :
    suzukiDF6D4FixedGridShard002OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 2 k) := by
  have h := suzukiDF6D4FixedGridShard002Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard002OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 2 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard002OddCross_eq_live :
    suzukiDF6D4FixedGridShard002OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 2) := by
  have h := suzukiDF6D4FixedGridShard002Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard002OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 2)) at h
  exact h

def suzukiDF6D4FixedGridShard002OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard002OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard002OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard002OddDotSoundness i.val
      suzukiDF6D4FixedGridShard002OddComparisonData)

theorem suzukiDF6D4FixedGridShard002OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard002OddSolveData =
      suzukiDF6D4FixedGridShard002OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard002Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard002OddSolveData =
    suzukiDF6D4FixedGridShard002OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard002OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard002OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 2 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 2 k) := by
    rw [suzukiDF6D4FixedGridShard002OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 2 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002OddDotSoundness i
          suzukiDF6D4FixedGridShard002OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 2 k) := by
    simpa [suzukiDF6D4FixedGridShard002OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard002OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 2 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 2) := by
    rw [suzukiDF6D4FixedGridShard002OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 2)
  rw [suzukiDF6D4FixedGridShard002OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard002OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard002OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard002OddDotSoundness i
            suzukiDF6D4FixedGridShard002OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard002OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard002EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard002EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 303) := by
  have h := suzukiDF6D4FixedGridShard002Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard002EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 303)) at h
  exact h

theorem suzukiDF6D4FixedGridShard002EvenFull_eq_live :
    suzukiDF6D4FixedGridShard002EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 303) := by
  have h := suzukiDF6D4FixedGridShard002Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard002EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 303)) at h
  exact h

def suzukiDF6D4FixedGridShard002EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard002EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard002EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard002EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard002EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard002EvenResidualData =
      suzukiDF6D4FixedGridShard002EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard002Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard002EvenResidualData =
    suzukiDF6D4FixedGridShard002EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard002EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard002EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 303 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 303) := by
    rw [suzukiDF6D4FixedGridShard002EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 303
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002EvenDotSoundness i
          suzukiDF6D4FixedGridShard002EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 303) := by
    simpa [suzukiDF6D4FixedGridShard002EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard002EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 303) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 303) := by
    rw [suzukiDF6D4FixedGridShard002EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 303
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard002EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard002EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard002EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard002EvenDotSoundness i
            suzukiDF6D4FixedGridShard002EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard002EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard002OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard002OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 303) := by
  have h := suzukiDF6D4FixedGridShard002Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard002OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 303)) at h
  exact h

theorem suzukiDF6D4FixedGridShard002OddFull_eq_live :
    suzukiDF6D4FixedGridShard002OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 303) := by
  have h := suzukiDF6D4FixedGridShard002Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard002OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 303)) at h
  exact h

def suzukiDF6D4FixedGridShard002OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard002OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard002OddDotSoundness i.val
        suzukiDF6D4FixedGridShard002OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard002OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard002OddResidualData =
      suzukiDF6D4FixedGridShard002OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard002Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard002OddResidualData =
    suzukiDF6D4FixedGridShard002OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard002OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard002OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 303 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 303) := by
    rw [suzukiDF6D4FixedGridShard002OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 303
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002OddDotSoundness i
          suzukiDF6D4FixedGridShard002OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 303) := by
    simpa [suzukiDF6D4FixedGridShard002OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard002OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 303) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard002OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 303) := by
    rw [suzukiDF6D4FixedGridShard002OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 303
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard002OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard002OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard002OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard002OddDotSoundness i
            suzukiDF6D4FixedGridShard002OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard002OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
