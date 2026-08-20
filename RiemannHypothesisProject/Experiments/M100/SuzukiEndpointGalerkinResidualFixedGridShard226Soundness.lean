import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard226Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard226Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard226EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard226EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 226 k) := by
  have h := suzukiDF6D4FixedGridShard226Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard226EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 226 k)) at h
  exact h

def suzukiDF6D4FixedGridShard226EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard226EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard226EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard226EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard226EvenComparisonData)

theorem suzukiDF6D4FixedGridShard226EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard226EvenSolveData =
      suzukiDF6D4FixedGridShard226EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard226Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard226EvenSolveData =
    suzukiDF6D4FixedGridShard226EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard226EvenCross_eq_live :
    suzukiDF6D4FixedGridShard226EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 226) := by
  have h := suzukiDF6D4FixedGridShard226Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard226EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 226)) at h
  exact h

theorem suzukiDF6D4FixedGridShard226EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard226EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 226 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 226 k) := by
    rw [suzukiDF6D4FixedGridShard226EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 226 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226EvenDotSoundness i
          suzukiDF6D4FixedGridShard226EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 226 k) := by
    simpa [suzukiDF6D4FixedGridShard226EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard226EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 226 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 226) := by
    rw [suzukiDF6D4FixedGridShard226EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 226)
  rw [suzukiDF6D4FixedGridShard226EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard226EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard226EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard226EvenDotSoundness i
            suzukiDF6D4FixedGridShard226EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard226EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard226OddComparison_eq_live :
    suzukiDF6D4FixedGridShard226OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 226 k) := by
  have h := suzukiDF6D4FixedGridShard226Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard226OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 226 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard226OddCross_eq_live :
    suzukiDF6D4FixedGridShard226OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 226) := by
  have h := suzukiDF6D4FixedGridShard226Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard226OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 226)) at h
  exact h

def suzukiDF6D4FixedGridShard226OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard226OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard226OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard226OddDotSoundness i.val
      suzukiDF6D4FixedGridShard226OddComparisonData)

theorem suzukiDF6D4FixedGridShard226OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard226OddSolveData =
      suzukiDF6D4FixedGridShard226OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard226Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard226OddSolveData =
    suzukiDF6D4FixedGridShard226OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard226OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard226OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 226 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 226 k) := by
    rw [suzukiDF6D4FixedGridShard226OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 226 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226OddDotSoundness i
          suzukiDF6D4FixedGridShard226OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 226 k) := by
    simpa [suzukiDF6D4FixedGridShard226OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard226OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 226 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 226) := by
    rw [suzukiDF6D4FixedGridShard226OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 226)
  rw [suzukiDF6D4FixedGridShard226OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard226OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard226OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard226OddDotSoundness i
            suzukiDF6D4FixedGridShard226OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard226OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard226EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard226EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 527) := by
  have h := suzukiDF6D4FixedGridShard226Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard226EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 527)) at h
  exact h

theorem suzukiDF6D4FixedGridShard226EvenFull_eq_live :
    suzukiDF6D4FixedGridShard226EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 527) := by
  have h := suzukiDF6D4FixedGridShard226Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard226EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 527)) at h
  exact h

def suzukiDF6D4FixedGridShard226EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard226EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard226EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard226EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard226EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard226EvenResidualData =
      suzukiDF6D4FixedGridShard226EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard226Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard226EvenResidualData =
    suzukiDF6D4FixedGridShard226EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard226EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard226EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 527 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 527) := by
    rw [suzukiDF6D4FixedGridShard226EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 527
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226EvenDotSoundness i
          suzukiDF6D4FixedGridShard226EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 527) := by
    simpa [suzukiDF6D4FixedGridShard226EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard226EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 527) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 527) := by
    rw [suzukiDF6D4FixedGridShard226EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 527
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard226EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard226EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard226EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard226EvenDotSoundness i
            suzukiDF6D4FixedGridShard226EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard226EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard226OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard226OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 527) := by
  have h := suzukiDF6D4FixedGridShard226Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard226OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 527)) at h
  exact h

theorem suzukiDF6D4FixedGridShard226OddFull_eq_live :
    suzukiDF6D4FixedGridShard226OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 527) := by
  have h := suzukiDF6D4FixedGridShard226Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard226OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 527)) at h
  exact h

def suzukiDF6D4FixedGridShard226OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard226OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard226OddDotSoundness i.val
        suzukiDF6D4FixedGridShard226OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard226OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard226OddResidualData =
      suzukiDF6D4FixedGridShard226OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard226Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard226OddResidualData =
    suzukiDF6D4FixedGridShard226OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard226OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard226OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 527 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 527) := by
    rw [suzukiDF6D4FixedGridShard226OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 527
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226OddDotSoundness i
          suzukiDF6D4FixedGridShard226OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 527) := by
    simpa [suzukiDF6D4FixedGridShard226OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard226OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 527) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard226OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 527) := by
    rw [suzukiDF6D4FixedGridShard226OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 527
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard226OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard226OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard226OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard226OddDotSoundness i
            suzukiDF6D4FixedGridShard226OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard226OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
