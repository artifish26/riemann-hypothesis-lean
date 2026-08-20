import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard215Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard215Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard215EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard215EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 215 k) := by
  have h := suzukiDF6D4FixedGridShard215Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard215EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 215 k)) at h
  exact h

def suzukiDF6D4FixedGridShard215EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard215EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard215EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard215EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard215EvenComparisonData)

theorem suzukiDF6D4FixedGridShard215EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard215EvenSolveData =
      suzukiDF6D4FixedGridShard215EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard215Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard215EvenSolveData =
    suzukiDF6D4FixedGridShard215EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard215EvenCross_eq_live :
    suzukiDF6D4FixedGridShard215EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 215) := by
  have h := suzukiDF6D4FixedGridShard215Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard215EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 215)) at h
  exact h

theorem suzukiDF6D4FixedGridShard215EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard215EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 215 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 215 k) := by
    rw [suzukiDF6D4FixedGridShard215EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 215 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215EvenDotSoundness i
          suzukiDF6D4FixedGridShard215EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 215 k) := by
    simpa [suzukiDF6D4FixedGridShard215EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard215EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 215 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 215) := by
    rw [suzukiDF6D4FixedGridShard215EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 215)
  rw [suzukiDF6D4FixedGridShard215EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard215EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard215EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard215EvenDotSoundness i
            suzukiDF6D4FixedGridShard215EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard215EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard215OddComparison_eq_live :
    suzukiDF6D4FixedGridShard215OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 215 k) := by
  have h := suzukiDF6D4FixedGridShard215Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard215OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 215 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard215OddCross_eq_live :
    suzukiDF6D4FixedGridShard215OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 215) := by
  have h := suzukiDF6D4FixedGridShard215Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard215OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 215)) at h
  exact h

def suzukiDF6D4FixedGridShard215OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard215OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard215OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard215OddDotSoundness i.val
      suzukiDF6D4FixedGridShard215OddComparisonData)

theorem suzukiDF6D4FixedGridShard215OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard215OddSolveData =
      suzukiDF6D4FixedGridShard215OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard215Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard215OddSolveData =
    suzukiDF6D4FixedGridShard215OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard215OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard215OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 215 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 215 k) := by
    rw [suzukiDF6D4FixedGridShard215OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 215 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215OddDotSoundness i
          suzukiDF6D4FixedGridShard215OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 215 k) := by
    simpa [suzukiDF6D4FixedGridShard215OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard215OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 215 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 215) := by
    rw [suzukiDF6D4FixedGridShard215OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 215)
  rw [suzukiDF6D4FixedGridShard215OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard215OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard215OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard215OddDotSoundness i
            suzukiDF6D4FixedGridShard215OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard215OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard215EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard215EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 516) := by
  have h := suzukiDF6D4FixedGridShard215Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard215EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 516)) at h
  exact h

theorem suzukiDF6D4FixedGridShard215EvenFull_eq_live :
    suzukiDF6D4FixedGridShard215EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 516) := by
  have h := suzukiDF6D4FixedGridShard215Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard215EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 516)) at h
  exact h

def suzukiDF6D4FixedGridShard215EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard215EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard215EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard215EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard215EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard215EvenResidualData =
      suzukiDF6D4FixedGridShard215EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard215Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard215EvenResidualData =
    suzukiDF6D4FixedGridShard215EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard215EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard215EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 516 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 516) := by
    rw [suzukiDF6D4FixedGridShard215EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 516
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215EvenDotSoundness i
          suzukiDF6D4FixedGridShard215EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 516) := by
    simpa [suzukiDF6D4FixedGridShard215EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard215EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 516) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 516) := by
    rw [suzukiDF6D4FixedGridShard215EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 516
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard215EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard215EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard215EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard215EvenDotSoundness i
            suzukiDF6D4FixedGridShard215EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard215EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard215OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard215OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 516) := by
  have h := suzukiDF6D4FixedGridShard215Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard215OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 516)) at h
  exact h

theorem suzukiDF6D4FixedGridShard215OddFull_eq_live :
    suzukiDF6D4FixedGridShard215OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 516) := by
  have h := suzukiDF6D4FixedGridShard215Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard215OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 516)) at h
  exact h

def suzukiDF6D4FixedGridShard215OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard215OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard215OddDotSoundness i.val
        suzukiDF6D4FixedGridShard215OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard215OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard215OddResidualData =
      suzukiDF6D4FixedGridShard215OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard215Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard215OddResidualData =
    suzukiDF6D4FixedGridShard215OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard215OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard215OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 516 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 516) := by
    rw [suzukiDF6D4FixedGridShard215OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 516
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215OddDotSoundness i
          suzukiDF6D4FixedGridShard215OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 516) := by
    simpa [suzukiDF6D4FixedGridShard215OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard215OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 516) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard215OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 516) := by
    rw [suzukiDF6D4FixedGridShard215OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 516
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard215OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard215OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard215OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard215OddDotSoundness i
            suzukiDF6D4FixedGridShard215OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard215OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
