import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard227Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard227Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard227EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard227EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 227 k) := by
  have h := suzukiDF6D4FixedGridShard227Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard227EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 227 k)) at h
  exact h

def suzukiDF6D4FixedGridShard227EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard227EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard227EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard227EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard227EvenComparisonData)

theorem suzukiDF6D4FixedGridShard227EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard227EvenSolveData =
      suzukiDF6D4FixedGridShard227EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard227Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard227EvenSolveData =
    suzukiDF6D4FixedGridShard227EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard227EvenCross_eq_live :
    suzukiDF6D4FixedGridShard227EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 227) := by
  have h := suzukiDF6D4FixedGridShard227Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard227EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 227)) at h
  exact h

theorem suzukiDF6D4FixedGridShard227EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard227EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 227 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 227 k) := by
    rw [suzukiDF6D4FixedGridShard227EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 227 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227EvenDotSoundness i
          suzukiDF6D4FixedGridShard227EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 227 k) := by
    simpa [suzukiDF6D4FixedGridShard227EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard227EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 227 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 227) := by
    rw [suzukiDF6D4FixedGridShard227EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 227)
  rw [suzukiDF6D4FixedGridShard227EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard227EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard227EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard227EvenDotSoundness i
            suzukiDF6D4FixedGridShard227EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard227EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard227OddComparison_eq_live :
    suzukiDF6D4FixedGridShard227OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 227 k) := by
  have h := suzukiDF6D4FixedGridShard227Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard227OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 227 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard227OddCross_eq_live :
    suzukiDF6D4FixedGridShard227OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 227) := by
  have h := suzukiDF6D4FixedGridShard227Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard227OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 227)) at h
  exact h

def suzukiDF6D4FixedGridShard227OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard227OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard227OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard227OddDotSoundness i.val
      suzukiDF6D4FixedGridShard227OddComparisonData)

theorem suzukiDF6D4FixedGridShard227OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard227OddSolveData =
      suzukiDF6D4FixedGridShard227OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard227Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard227OddSolveData =
    suzukiDF6D4FixedGridShard227OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard227OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard227OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 227 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 227 k) := by
    rw [suzukiDF6D4FixedGridShard227OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 227 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227OddDotSoundness i
          suzukiDF6D4FixedGridShard227OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 227 k) := by
    simpa [suzukiDF6D4FixedGridShard227OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard227OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 227 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 227) := by
    rw [suzukiDF6D4FixedGridShard227OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 227)
  rw [suzukiDF6D4FixedGridShard227OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard227OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard227OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard227OddDotSoundness i
            suzukiDF6D4FixedGridShard227OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard227OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard227EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard227EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 528) := by
  have h := suzukiDF6D4FixedGridShard227Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard227EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 528)) at h
  exact h

theorem suzukiDF6D4FixedGridShard227EvenFull_eq_live :
    suzukiDF6D4FixedGridShard227EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 528) := by
  have h := suzukiDF6D4FixedGridShard227Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard227EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 528)) at h
  exact h

def suzukiDF6D4FixedGridShard227EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard227EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard227EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard227EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard227EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard227EvenResidualData =
      suzukiDF6D4FixedGridShard227EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard227Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard227EvenResidualData =
    suzukiDF6D4FixedGridShard227EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard227EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard227EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 528 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 528) := by
    rw [suzukiDF6D4FixedGridShard227EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 528
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227EvenDotSoundness i
          suzukiDF6D4FixedGridShard227EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 528) := by
    simpa [suzukiDF6D4FixedGridShard227EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard227EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 528) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 528) := by
    rw [suzukiDF6D4FixedGridShard227EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 528
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard227EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard227EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard227EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard227EvenDotSoundness i
            suzukiDF6D4FixedGridShard227EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard227EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard227OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard227OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 528) := by
  have h := suzukiDF6D4FixedGridShard227Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard227OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 528)) at h
  exact h

theorem suzukiDF6D4FixedGridShard227OddFull_eq_live :
    suzukiDF6D4FixedGridShard227OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 528) := by
  have h := suzukiDF6D4FixedGridShard227Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard227OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 528)) at h
  exact h

def suzukiDF6D4FixedGridShard227OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard227OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard227OddDotSoundness i.val
        suzukiDF6D4FixedGridShard227OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard227OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard227OddResidualData =
      suzukiDF6D4FixedGridShard227OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard227Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard227OddResidualData =
    suzukiDF6D4FixedGridShard227OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard227OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard227OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 528 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 528) := by
    rw [suzukiDF6D4FixedGridShard227OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 528
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227OddDotSoundness i
          suzukiDF6D4FixedGridShard227OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 528) := by
    simpa [suzukiDF6D4FixedGridShard227OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard227OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 528) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard227OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 528) := by
    rw [suzukiDF6D4FixedGridShard227OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 528
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard227OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard227OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard227OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard227OddDotSoundness i
            suzukiDF6D4FixedGridShard227OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard227OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
