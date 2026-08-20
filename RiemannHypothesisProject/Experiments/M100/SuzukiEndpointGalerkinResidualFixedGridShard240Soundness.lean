import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard240Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard240Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard240EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard240EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 240 k) := by
  have h := suzukiDF6D4FixedGridShard240Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard240EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 240 k)) at h
  exact h

def suzukiDF6D4FixedGridShard240EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard240EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard240EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard240EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard240EvenComparisonData)

theorem suzukiDF6D4FixedGridShard240EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard240EvenSolveData =
      suzukiDF6D4FixedGridShard240EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard240Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard240EvenSolveData =
    suzukiDF6D4FixedGridShard240EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard240EvenCross_eq_live :
    suzukiDF6D4FixedGridShard240EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 240) := by
  have h := suzukiDF6D4FixedGridShard240Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard240EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 240)) at h
  exact h

theorem suzukiDF6D4FixedGridShard240EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard240EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 240 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 240 k) := by
    rw [suzukiDF6D4FixedGridShard240EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 240 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240EvenDotSoundness i
          suzukiDF6D4FixedGridShard240EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 240 k) := by
    simpa [suzukiDF6D4FixedGridShard240EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard240EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 240 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 240) := by
    rw [suzukiDF6D4FixedGridShard240EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 240)
  rw [suzukiDF6D4FixedGridShard240EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard240EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard240EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard240EvenDotSoundness i
            suzukiDF6D4FixedGridShard240EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard240EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard240OddComparison_eq_live :
    suzukiDF6D4FixedGridShard240OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 240 k) := by
  have h := suzukiDF6D4FixedGridShard240Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard240OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 240 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard240OddCross_eq_live :
    suzukiDF6D4FixedGridShard240OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 240) := by
  have h := suzukiDF6D4FixedGridShard240Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard240OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 240)) at h
  exact h

def suzukiDF6D4FixedGridShard240OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard240OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard240OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard240OddDotSoundness i.val
      suzukiDF6D4FixedGridShard240OddComparisonData)

theorem suzukiDF6D4FixedGridShard240OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard240OddSolveData =
      suzukiDF6D4FixedGridShard240OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard240Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard240OddSolveData =
    suzukiDF6D4FixedGridShard240OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard240OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard240OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 240 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 240 k) := by
    rw [suzukiDF6D4FixedGridShard240OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 240 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240OddDotSoundness i
          suzukiDF6D4FixedGridShard240OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 240 k) := by
    simpa [suzukiDF6D4FixedGridShard240OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard240OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 240 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 240) := by
    rw [suzukiDF6D4FixedGridShard240OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 240)
  rw [suzukiDF6D4FixedGridShard240OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard240OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard240OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard240OddDotSoundness i
            suzukiDF6D4FixedGridShard240OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard240OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard240EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard240EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 541) := by
  have h := suzukiDF6D4FixedGridShard240Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard240EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 541)) at h
  exact h

theorem suzukiDF6D4FixedGridShard240EvenFull_eq_live :
    suzukiDF6D4FixedGridShard240EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 541) := by
  have h := suzukiDF6D4FixedGridShard240Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard240EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 541)) at h
  exact h

def suzukiDF6D4FixedGridShard240EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard240EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard240EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard240EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard240EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard240EvenResidualData =
      suzukiDF6D4FixedGridShard240EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard240Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard240EvenResidualData =
    suzukiDF6D4FixedGridShard240EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard240EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard240EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 541 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 541) := by
    rw [suzukiDF6D4FixedGridShard240EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 541
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240EvenDotSoundness i
          suzukiDF6D4FixedGridShard240EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 541) := by
    simpa [suzukiDF6D4FixedGridShard240EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard240EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 541) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 541) := by
    rw [suzukiDF6D4FixedGridShard240EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 541
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard240EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard240EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard240EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard240EvenDotSoundness i
            suzukiDF6D4FixedGridShard240EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard240EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard240OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard240OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 541) := by
  have h := suzukiDF6D4FixedGridShard240Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard240OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 541)) at h
  exact h

theorem suzukiDF6D4FixedGridShard240OddFull_eq_live :
    suzukiDF6D4FixedGridShard240OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 541) := by
  have h := suzukiDF6D4FixedGridShard240Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard240OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 541)) at h
  exact h

def suzukiDF6D4FixedGridShard240OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard240OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard240OddDotSoundness i.val
        suzukiDF6D4FixedGridShard240OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard240OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard240OddResidualData =
      suzukiDF6D4FixedGridShard240OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard240Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard240OddResidualData =
    suzukiDF6D4FixedGridShard240OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard240OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard240OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 541 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 541) := by
    rw [suzukiDF6D4FixedGridShard240OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 541
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240OddDotSoundness i
          suzukiDF6D4FixedGridShard240OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 541) := by
    simpa [suzukiDF6D4FixedGridShard240OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard240OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 541) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard240OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 541) := by
    rw [suzukiDF6D4FixedGridShard240OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 541
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard240OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard240OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard240OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard240OddDotSoundness i
            suzukiDF6D4FixedGridShard240OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard240OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
