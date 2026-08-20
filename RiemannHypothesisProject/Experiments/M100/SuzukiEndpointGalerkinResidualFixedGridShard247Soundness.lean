import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard247Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard247Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard247EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard247EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 247 k) := by
  have h := suzukiDF6D4FixedGridShard247Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard247EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 247 k)) at h
  exact h

def suzukiDF6D4FixedGridShard247EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard247EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard247EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard247EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard247EvenComparisonData)

theorem suzukiDF6D4FixedGridShard247EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard247EvenSolveData =
      suzukiDF6D4FixedGridShard247EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard247Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard247EvenSolveData =
    suzukiDF6D4FixedGridShard247EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard247EvenCross_eq_live :
    suzukiDF6D4FixedGridShard247EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 247) := by
  have h := suzukiDF6D4FixedGridShard247Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard247EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 247)) at h
  exact h

theorem suzukiDF6D4FixedGridShard247EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard247EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 247 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 247 k) := by
    rw [suzukiDF6D4FixedGridShard247EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 247 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247EvenDotSoundness i
          suzukiDF6D4FixedGridShard247EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 247 k) := by
    simpa [suzukiDF6D4FixedGridShard247EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard247EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 247 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 247) := by
    rw [suzukiDF6D4FixedGridShard247EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 247)
  rw [suzukiDF6D4FixedGridShard247EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard247EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard247EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard247EvenDotSoundness i
            suzukiDF6D4FixedGridShard247EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard247EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard247OddComparison_eq_live :
    suzukiDF6D4FixedGridShard247OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 247 k) := by
  have h := suzukiDF6D4FixedGridShard247Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard247OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 247 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard247OddCross_eq_live :
    suzukiDF6D4FixedGridShard247OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 247) := by
  have h := suzukiDF6D4FixedGridShard247Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard247OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 247)) at h
  exact h

def suzukiDF6D4FixedGridShard247OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard247OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard247OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard247OddDotSoundness i.val
      suzukiDF6D4FixedGridShard247OddComparisonData)

theorem suzukiDF6D4FixedGridShard247OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard247OddSolveData =
      suzukiDF6D4FixedGridShard247OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard247Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard247OddSolveData =
    suzukiDF6D4FixedGridShard247OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard247OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard247OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 247 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 247 k) := by
    rw [suzukiDF6D4FixedGridShard247OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 247 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247OddDotSoundness i
          suzukiDF6D4FixedGridShard247OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 247 k) := by
    simpa [suzukiDF6D4FixedGridShard247OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard247OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 247 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 247) := by
    rw [suzukiDF6D4FixedGridShard247OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 247)
  rw [suzukiDF6D4FixedGridShard247OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard247OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard247OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard247OddDotSoundness i
            suzukiDF6D4FixedGridShard247OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard247OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard247EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard247EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 548) := by
  have h := suzukiDF6D4FixedGridShard247Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard247EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 548)) at h
  exact h

theorem suzukiDF6D4FixedGridShard247EvenFull_eq_live :
    suzukiDF6D4FixedGridShard247EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 548) := by
  have h := suzukiDF6D4FixedGridShard247Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard247EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 548)) at h
  exact h

def suzukiDF6D4FixedGridShard247EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard247EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard247EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard247EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard247EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard247EvenResidualData =
      suzukiDF6D4FixedGridShard247EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard247Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard247EvenResidualData =
    suzukiDF6D4FixedGridShard247EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard247EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard247EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 548 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 548) := by
    rw [suzukiDF6D4FixedGridShard247EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 548
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247EvenDotSoundness i
          suzukiDF6D4FixedGridShard247EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 548) := by
    simpa [suzukiDF6D4FixedGridShard247EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard247EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 548) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 548) := by
    rw [suzukiDF6D4FixedGridShard247EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 548
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard247EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard247EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard247EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard247EvenDotSoundness i
            suzukiDF6D4FixedGridShard247EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard247EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard247OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard247OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 548) := by
  have h := suzukiDF6D4FixedGridShard247Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard247OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 548)) at h
  exact h

theorem suzukiDF6D4FixedGridShard247OddFull_eq_live :
    suzukiDF6D4FixedGridShard247OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 548) := by
  have h := suzukiDF6D4FixedGridShard247Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard247OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 548)) at h
  exact h

def suzukiDF6D4FixedGridShard247OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard247OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard247OddDotSoundness i.val
        suzukiDF6D4FixedGridShard247OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard247OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard247OddResidualData =
      suzukiDF6D4FixedGridShard247OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard247Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard247OddResidualData =
    suzukiDF6D4FixedGridShard247OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard247OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard247OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 548 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 548) := by
    rw [suzukiDF6D4FixedGridShard247OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 548
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247OddDotSoundness i
          suzukiDF6D4FixedGridShard247OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 548) := by
    simpa [suzukiDF6D4FixedGridShard247OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard247OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 548) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard247OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 548) := by
    rw [suzukiDF6D4FixedGridShard247OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 548
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard247OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard247OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard247OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard247OddDotSoundness i
            suzukiDF6D4FixedGridShard247OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard247OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
