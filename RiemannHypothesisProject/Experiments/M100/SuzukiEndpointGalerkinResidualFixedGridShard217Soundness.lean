import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard217Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard217Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard217EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard217EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 217 k) := by
  have h := suzukiDF6D4FixedGridShard217Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard217EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 217 k)) at h
  exact h

def suzukiDF6D4FixedGridShard217EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard217EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard217EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard217EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard217EvenComparisonData)

theorem suzukiDF6D4FixedGridShard217EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard217EvenSolveData =
      suzukiDF6D4FixedGridShard217EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard217Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard217EvenSolveData =
    suzukiDF6D4FixedGridShard217EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard217EvenCross_eq_live :
    suzukiDF6D4FixedGridShard217EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 217) := by
  have h := suzukiDF6D4FixedGridShard217Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard217EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 217)) at h
  exact h

theorem suzukiDF6D4FixedGridShard217EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard217EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 217 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 217 k) := by
    rw [suzukiDF6D4FixedGridShard217EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 217 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217EvenDotSoundness i
          suzukiDF6D4FixedGridShard217EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 217 k) := by
    simpa [suzukiDF6D4FixedGridShard217EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard217EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 217 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 217) := by
    rw [suzukiDF6D4FixedGridShard217EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 217)
  rw [suzukiDF6D4FixedGridShard217EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard217EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard217EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard217EvenDotSoundness i
            suzukiDF6D4FixedGridShard217EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard217EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard217OddComparison_eq_live :
    suzukiDF6D4FixedGridShard217OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 217 k) := by
  have h := suzukiDF6D4FixedGridShard217Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard217OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 217 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard217OddCross_eq_live :
    suzukiDF6D4FixedGridShard217OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 217) := by
  have h := suzukiDF6D4FixedGridShard217Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard217OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 217)) at h
  exact h

def suzukiDF6D4FixedGridShard217OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard217OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard217OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard217OddDotSoundness i.val
      suzukiDF6D4FixedGridShard217OddComparisonData)

theorem suzukiDF6D4FixedGridShard217OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard217OddSolveData =
      suzukiDF6D4FixedGridShard217OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard217Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard217OddSolveData =
    suzukiDF6D4FixedGridShard217OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard217OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard217OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 217 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 217 k) := by
    rw [suzukiDF6D4FixedGridShard217OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 217 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217OddDotSoundness i
          suzukiDF6D4FixedGridShard217OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 217 k) := by
    simpa [suzukiDF6D4FixedGridShard217OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard217OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 217 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 217) := by
    rw [suzukiDF6D4FixedGridShard217OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 217)
  rw [suzukiDF6D4FixedGridShard217OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard217OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard217OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard217OddDotSoundness i
            suzukiDF6D4FixedGridShard217OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard217OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard217EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard217EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 518) := by
  have h := suzukiDF6D4FixedGridShard217Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard217EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 518)) at h
  exact h

theorem suzukiDF6D4FixedGridShard217EvenFull_eq_live :
    suzukiDF6D4FixedGridShard217EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 518) := by
  have h := suzukiDF6D4FixedGridShard217Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard217EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 518)) at h
  exact h

def suzukiDF6D4FixedGridShard217EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard217EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard217EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard217EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard217EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard217EvenResidualData =
      suzukiDF6D4FixedGridShard217EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard217Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard217EvenResidualData =
    suzukiDF6D4FixedGridShard217EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard217EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard217EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 518 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 518) := by
    rw [suzukiDF6D4FixedGridShard217EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 518
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217EvenDotSoundness i
          suzukiDF6D4FixedGridShard217EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 518) := by
    simpa [suzukiDF6D4FixedGridShard217EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard217EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 518) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 518) := by
    rw [suzukiDF6D4FixedGridShard217EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 518
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard217EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard217EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard217EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard217EvenDotSoundness i
            suzukiDF6D4FixedGridShard217EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard217EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard217OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard217OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 518) := by
  have h := suzukiDF6D4FixedGridShard217Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard217OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 518)) at h
  exact h

theorem suzukiDF6D4FixedGridShard217OddFull_eq_live :
    suzukiDF6D4FixedGridShard217OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 518) := by
  have h := suzukiDF6D4FixedGridShard217Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard217OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 518)) at h
  exact h

def suzukiDF6D4FixedGridShard217OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard217OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard217OddDotSoundness i.val
        suzukiDF6D4FixedGridShard217OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard217OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard217OddResidualData =
      suzukiDF6D4FixedGridShard217OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard217Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard217OddResidualData =
    suzukiDF6D4FixedGridShard217OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard217OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard217OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 518 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 518) := by
    rw [suzukiDF6D4FixedGridShard217OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 518
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217OddDotSoundness i
          suzukiDF6D4FixedGridShard217OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 518) := by
    simpa [suzukiDF6D4FixedGridShard217OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard217OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 518) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard217OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 518) := by
    rw [suzukiDF6D4FixedGridShard217OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 518
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard217OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard217OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard217OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard217OddDotSoundness i
            suzukiDF6D4FixedGridShard217OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard217OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
