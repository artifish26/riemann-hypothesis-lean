import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard223Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard223Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard223EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard223EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 223 k) := by
  have h := suzukiDF6D4FixedGridShard223Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard223EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 223 k)) at h
  exact h

def suzukiDF6D4FixedGridShard223EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard223EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard223EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard223EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard223EvenComparisonData)

theorem suzukiDF6D4FixedGridShard223EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard223EvenSolveData =
      suzukiDF6D4FixedGridShard223EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard223Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard223EvenSolveData =
    suzukiDF6D4FixedGridShard223EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard223EvenCross_eq_live :
    suzukiDF6D4FixedGridShard223EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 223) := by
  have h := suzukiDF6D4FixedGridShard223Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard223EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 223)) at h
  exact h

theorem suzukiDF6D4FixedGridShard223EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard223EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 223 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 223 k) := by
    rw [suzukiDF6D4FixedGridShard223EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 223 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223EvenDotSoundness i
          suzukiDF6D4FixedGridShard223EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 223 k) := by
    simpa [suzukiDF6D4FixedGridShard223EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard223EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 223 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 223) := by
    rw [suzukiDF6D4FixedGridShard223EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 223)
  rw [suzukiDF6D4FixedGridShard223EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard223EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard223EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard223EvenDotSoundness i
            suzukiDF6D4FixedGridShard223EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard223EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard223OddComparison_eq_live :
    suzukiDF6D4FixedGridShard223OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 223 k) := by
  have h := suzukiDF6D4FixedGridShard223Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard223OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 223 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard223OddCross_eq_live :
    suzukiDF6D4FixedGridShard223OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 223) := by
  have h := suzukiDF6D4FixedGridShard223Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard223OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 223)) at h
  exact h

def suzukiDF6D4FixedGridShard223OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard223OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard223OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard223OddDotSoundness i.val
      suzukiDF6D4FixedGridShard223OddComparisonData)

theorem suzukiDF6D4FixedGridShard223OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard223OddSolveData =
      suzukiDF6D4FixedGridShard223OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard223Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard223OddSolveData =
    suzukiDF6D4FixedGridShard223OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard223OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard223OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 223 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 223 k) := by
    rw [suzukiDF6D4FixedGridShard223OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 223 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223OddDotSoundness i
          suzukiDF6D4FixedGridShard223OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 223 k) := by
    simpa [suzukiDF6D4FixedGridShard223OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard223OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 223 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 223) := by
    rw [suzukiDF6D4FixedGridShard223OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 223)
  rw [suzukiDF6D4FixedGridShard223OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard223OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard223OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard223OddDotSoundness i
            suzukiDF6D4FixedGridShard223OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard223OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard223EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard223EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 524) := by
  have h := suzukiDF6D4FixedGridShard223Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard223EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 524)) at h
  exact h

theorem suzukiDF6D4FixedGridShard223EvenFull_eq_live :
    suzukiDF6D4FixedGridShard223EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 524) := by
  have h := suzukiDF6D4FixedGridShard223Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard223EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 524)) at h
  exact h

def suzukiDF6D4FixedGridShard223EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard223EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard223EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard223EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard223EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard223EvenResidualData =
      suzukiDF6D4FixedGridShard223EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard223Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard223EvenResidualData =
    suzukiDF6D4FixedGridShard223EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard223EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard223EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 524 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 524) := by
    rw [suzukiDF6D4FixedGridShard223EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 524
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223EvenDotSoundness i
          suzukiDF6D4FixedGridShard223EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 524) := by
    simpa [suzukiDF6D4FixedGridShard223EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard223EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 524) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 524) := by
    rw [suzukiDF6D4FixedGridShard223EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 524
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard223EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard223EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard223EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard223EvenDotSoundness i
            suzukiDF6D4FixedGridShard223EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard223EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard223OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard223OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 524) := by
  have h := suzukiDF6D4FixedGridShard223Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard223OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 524)) at h
  exact h

theorem suzukiDF6D4FixedGridShard223OddFull_eq_live :
    suzukiDF6D4FixedGridShard223OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 524) := by
  have h := suzukiDF6D4FixedGridShard223Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard223OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 524)) at h
  exact h

def suzukiDF6D4FixedGridShard223OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard223OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard223OddDotSoundness i.val
        suzukiDF6D4FixedGridShard223OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard223OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard223OddResidualData =
      suzukiDF6D4FixedGridShard223OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard223Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard223OddResidualData =
    suzukiDF6D4FixedGridShard223OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard223OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard223OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 524 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 524) := by
    rw [suzukiDF6D4FixedGridShard223OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 524
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223OddDotSoundness i
          suzukiDF6D4FixedGridShard223OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 524) := by
    simpa [suzukiDF6D4FixedGridShard223OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard223OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 524) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard223OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 524) := by
    rw [suzukiDF6D4FixedGridShard223OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 524
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard223OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard223OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard223OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard223OddDotSoundness i
            suzukiDF6D4FixedGridShard223OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard223OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
