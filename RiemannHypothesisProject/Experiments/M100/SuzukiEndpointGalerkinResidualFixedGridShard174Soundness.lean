import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard174Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard174Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard174EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard174EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 174 k) := by
  have h := suzukiDF6D4FixedGridShard174Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard174EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 174 k)) at h
  exact h

def suzukiDF6D4FixedGridShard174EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard174EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard174EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard174EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard174EvenComparisonData)

theorem suzukiDF6D4FixedGridShard174EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard174EvenSolveData =
      suzukiDF6D4FixedGridShard174EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard174Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard174EvenSolveData =
    suzukiDF6D4FixedGridShard174EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard174EvenCross_eq_live :
    suzukiDF6D4FixedGridShard174EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 174) := by
  have h := suzukiDF6D4FixedGridShard174Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard174EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 174)) at h
  exact h

theorem suzukiDF6D4FixedGridShard174EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard174EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 174 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 174 k) := by
    rw [suzukiDF6D4FixedGridShard174EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 174 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174EvenDotSoundness i
          suzukiDF6D4FixedGridShard174EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 174 k) := by
    simpa [suzukiDF6D4FixedGridShard174EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard174EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 174 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 174) := by
    rw [suzukiDF6D4FixedGridShard174EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 174)
  rw [suzukiDF6D4FixedGridShard174EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard174EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard174EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard174EvenDotSoundness i
            suzukiDF6D4FixedGridShard174EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard174EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard174OddComparison_eq_live :
    suzukiDF6D4FixedGridShard174OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 174 k) := by
  have h := suzukiDF6D4FixedGridShard174Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard174OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 174 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard174OddCross_eq_live :
    suzukiDF6D4FixedGridShard174OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 174) := by
  have h := suzukiDF6D4FixedGridShard174Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard174OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 174)) at h
  exact h

def suzukiDF6D4FixedGridShard174OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard174OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard174OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard174OddDotSoundness i.val
      suzukiDF6D4FixedGridShard174OddComparisonData)

theorem suzukiDF6D4FixedGridShard174OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard174OddSolveData =
      suzukiDF6D4FixedGridShard174OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard174Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard174OddSolveData =
    suzukiDF6D4FixedGridShard174OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard174OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard174OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 174 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 174 k) := by
    rw [suzukiDF6D4FixedGridShard174OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 174 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174OddDotSoundness i
          suzukiDF6D4FixedGridShard174OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 174 k) := by
    simpa [suzukiDF6D4FixedGridShard174OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard174OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 174 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 174) := by
    rw [suzukiDF6D4FixedGridShard174OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 174)
  rw [suzukiDF6D4FixedGridShard174OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard174OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard174OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard174OddDotSoundness i
            suzukiDF6D4FixedGridShard174OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard174OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard174EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard174EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 475) := by
  have h := suzukiDF6D4FixedGridShard174Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard174EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 475)) at h
  exact h

theorem suzukiDF6D4FixedGridShard174EvenFull_eq_live :
    suzukiDF6D4FixedGridShard174EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 475) := by
  have h := suzukiDF6D4FixedGridShard174Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard174EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 475)) at h
  exact h

def suzukiDF6D4FixedGridShard174EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard174EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard174EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard174EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard174EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard174EvenResidualData =
      suzukiDF6D4FixedGridShard174EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard174Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard174EvenResidualData =
    suzukiDF6D4FixedGridShard174EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard174EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard174EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 475 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 475) := by
    rw [suzukiDF6D4FixedGridShard174EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 475
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174EvenDotSoundness i
          suzukiDF6D4FixedGridShard174EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 475) := by
    simpa [suzukiDF6D4FixedGridShard174EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard174EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 475) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 475) := by
    rw [suzukiDF6D4FixedGridShard174EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 475
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard174EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard174EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard174EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard174EvenDotSoundness i
            suzukiDF6D4FixedGridShard174EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard174EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard174OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard174OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 475) := by
  have h := suzukiDF6D4FixedGridShard174Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard174OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 475)) at h
  exact h

theorem suzukiDF6D4FixedGridShard174OddFull_eq_live :
    suzukiDF6D4FixedGridShard174OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 475) := by
  have h := suzukiDF6D4FixedGridShard174Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard174OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 475)) at h
  exact h

def suzukiDF6D4FixedGridShard174OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard174OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard174OddDotSoundness i.val
        suzukiDF6D4FixedGridShard174OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard174OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard174OddResidualData =
      suzukiDF6D4FixedGridShard174OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard174Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard174OddResidualData =
    suzukiDF6D4FixedGridShard174OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard174OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard174OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 475 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 475) := by
    rw [suzukiDF6D4FixedGridShard174OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 475
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174OddDotSoundness i
          suzukiDF6D4FixedGridShard174OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 475) := by
    simpa [suzukiDF6D4FixedGridShard174OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard174OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 475) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard174OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 475) := by
    rw [suzukiDF6D4FixedGridShard174OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 475
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard174OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard174OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard174OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard174OddDotSoundness i
            suzukiDF6D4FixedGridShard174OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard174OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
