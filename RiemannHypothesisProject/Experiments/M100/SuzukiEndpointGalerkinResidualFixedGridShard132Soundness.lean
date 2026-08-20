import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard132Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard132Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard132EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard132EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 132 k) := by
  have h := suzukiDF6D4FixedGridShard132Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard132EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 132 k)) at h
  exact h

def suzukiDF6D4FixedGridShard132EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard132EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard132EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard132EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard132EvenComparisonData)

theorem suzukiDF6D4FixedGridShard132EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard132EvenSolveData =
      suzukiDF6D4FixedGridShard132EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard132Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard132EvenSolveData =
    suzukiDF6D4FixedGridShard132EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard132EvenCross_eq_live :
    suzukiDF6D4FixedGridShard132EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 132) := by
  have h := suzukiDF6D4FixedGridShard132Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard132EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 132)) at h
  exact h

theorem suzukiDF6D4FixedGridShard132EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard132EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 132 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 132 k) := by
    rw [suzukiDF6D4FixedGridShard132EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 132 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132EvenDotSoundness i
          suzukiDF6D4FixedGridShard132EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 132 k) := by
    simpa [suzukiDF6D4FixedGridShard132EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard132EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 132 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 132) := by
    rw [suzukiDF6D4FixedGridShard132EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 132)
  rw [suzukiDF6D4FixedGridShard132EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard132EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard132EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard132EvenDotSoundness i
            suzukiDF6D4FixedGridShard132EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard132EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard132OddComparison_eq_live :
    suzukiDF6D4FixedGridShard132OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 132 k) := by
  have h := suzukiDF6D4FixedGridShard132Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard132OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 132 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard132OddCross_eq_live :
    suzukiDF6D4FixedGridShard132OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 132) := by
  have h := suzukiDF6D4FixedGridShard132Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard132OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 132)) at h
  exact h

def suzukiDF6D4FixedGridShard132OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard132OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard132OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard132OddDotSoundness i.val
      suzukiDF6D4FixedGridShard132OddComparisonData)

theorem suzukiDF6D4FixedGridShard132OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard132OddSolveData =
      suzukiDF6D4FixedGridShard132OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard132Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard132OddSolveData =
    suzukiDF6D4FixedGridShard132OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard132OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard132OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 132 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 132 k) := by
    rw [suzukiDF6D4FixedGridShard132OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 132 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132OddDotSoundness i
          suzukiDF6D4FixedGridShard132OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 132 k) := by
    simpa [suzukiDF6D4FixedGridShard132OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard132OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 132 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 132) := by
    rw [suzukiDF6D4FixedGridShard132OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 132)
  rw [suzukiDF6D4FixedGridShard132OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard132OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard132OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard132OddDotSoundness i
            suzukiDF6D4FixedGridShard132OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard132OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard132EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard132EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 433) := by
  have h := suzukiDF6D4FixedGridShard132Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard132EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 433)) at h
  exact h

theorem suzukiDF6D4FixedGridShard132EvenFull_eq_live :
    suzukiDF6D4FixedGridShard132EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 433) := by
  have h := suzukiDF6D4FixedGridShard132Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard132EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 433)) at h
  exact h

def suzukiDF6D4FixedGridShard132EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard132EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard132EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard132EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard132EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard132EvenResidualData =
      suzukiDF6D4FixedGridShard132EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard132Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard132EvenResidualData =
    suzukiDF6D4FixedGridShard132EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard132EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard132EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 433 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 433) := by
    rw [suzukiDF6D4FixedGridShard132EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 433
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132EvenDotSoundness i
          suzukiDF6D4FixedGridShard132EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 433) := by
    simpa [suzukiDF6D4FixedGridShard132EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard132EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 433) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 433) := by
    rw [suzukiDF6D4FixedGridShard132EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 433
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard132EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard132EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard132EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard132EvenDotSoundness i
            suzukiDF6D4FixedGridShard132EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard132EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard132OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard132OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 433) := by
  have h := suzukiDF6D4FixedGridShard132Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard132OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 433)) at h
  exact h

theorem suzukiDF6D4FixedGridShard132OddFull_eq_live :
    suzukiDF6D4FixedGridShard132OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 433) := by
  have h := suzukiDF6D4FixedGridShard132Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard132OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 433)) at h
  exact h

def suzukiDF6D4FixedGridShard132OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard132OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard132OddDotSoundness i.val
        suzukiDF6D4FixedGridShard132OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard132OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard132OddResidualData =
      suzukiDF6D4FixedGridShard132OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard132Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard132OddResidualData =
    suzukiDF6D4FixedGridShard132OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard132OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard132OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 433 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 433) := by
    rw [suzukiDF6D4FixedGridShard132OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 433
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132OddDotSoundness i
          suzukiDF6D4FixedGridShard132OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 433) := by
    simpa [suzukiDF6D4FixedGridShard132OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard132OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 433) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard132OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 433) := by
    rw [suzukiDF6D4FixedGridShard132OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 433
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard132OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard132OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard132OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard132OddDotSoundness i
            suzukiDF6D4FixedGridShard132OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard132OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
