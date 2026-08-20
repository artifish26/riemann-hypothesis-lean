import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard231Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard231Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard231EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard231EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 231 k) := by
  have h := suzukiDF6D4FixedGridShard231Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard231EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 231 k)) at h
  exact h

def suzukiDF6D4FixedGridShard231EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard231EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard231EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard231EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard231EvenComparisonData)

theorem suzukiDF6D4FixedGridShard231EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard231EvenSolveData =
      suzukiDF6D4FixedGridShard231EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard231Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard231EvenSolveData =
    suzukiDF6D4FixedGridShard231EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard231EvenCross_eq_live :
    suzukiDF6D4FixedGridShard231EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 231) := by
  have h := suzukiDF6D4FixedGridShard231Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard231EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 231)) at h
  exact h

theorem suzukiDF6D4FixedGridShard231EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard231EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 231 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 231 k) := by
    rw [suzukiDF6D4FixedGridShard231EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 231 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231EvenDotSoundness i
          suzukiDF6D4FixedGridShard231EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 231 k) := by
    simpa [suzukiDF6D4FixedGridShard231EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard231EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 231 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 231) := by
    rw [suzukiDF6D4FixedGridShard231EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 231)
  rw [suzukiDF6D4FixedGridShard231EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard231EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard231EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard231EvenDotSoundness i
            suzukiDF6D4FixedGridShard231EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard231EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard231OddComparison_eq_live :
    suzukiDF6D4FixedGridShard231OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 231 k) := by
  have h := suzukiDF6D4FixedGridShard231Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard231OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 231 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard231OddCross_eq_live :
    suzukiDF6D4FixedGridShard231OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 231) := by
  have h := suzukiDF6D4FixedGridShard231Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard231OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 231)) at h
  exact h

def suzukiDF6D4FixedGridShard231OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard231OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard231OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard231OddDotSoundness i.val
      suzukiDF6D4FixedGridShard231OddComparisonData)

theorem suzukiDF6D4FixedGridShard231OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard231OddSolveData =
      suzukiDF6D4FixedGridShard231OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard231Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard231OddSolveData =
    suzukiDF6D4FixedGridShard231OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard231OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard231OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 231 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 231 k) := by
    rw [suzukiDF6D4FixedGridShard231OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 231 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231OddDotSoundness i
          suzukiDF6D4FixedGridShard231OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 231 k) := by
    simpa [suzukiDF6D4FixedGridShard231OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard231OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 231 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 231) := by
    rw [suzukiDF6D4FixedGridShard231OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 231)
  rw [suzukiDF6D4FixedGridShard231OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard231OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard231OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard231OddDotSoundness i
            suzukiDF6D4FixedGridShard231OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard231OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard231EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard231EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 532) := by
  have h := suzukiDF6D4FixedGridShard231Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard231EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 532)) at h
  exact h

theorem suzukiDF6D4FixedGridShard231EvenFull_eq_live :
    suzukiDF6D4FixedGridShard231EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 532) := by
  have h := suzukiDF6D4FixedGridShard231Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard231EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 532)) at h
  exact h

def suzukiDF6D4FixedGridShard231EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard231EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard231EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard231EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard231EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard231EvenResidualData =
      suzukiDF6D4FixedGridShard231EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard231Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard231EvenResidualData =
    suzukiDF6D4FixedGridShard231EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard231EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard231EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 532 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 532) := by
    rw [suzukiDF6D4FixedGridShard231EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 532
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231EvenDotSoundness i
          suzukiDF6D4FixedGridShard231EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 532) := by
    simpa [suzukiDF6D4FixedGridShard231EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard231EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 532) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 532) := by
    rw [suzukiDF6D4FixedGridShard231EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 532
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard231EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard231EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard231EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard231EvenDotSoundness i
            suzukiDF6D4FixedGridShard231EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard231EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard231OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard231OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 532) := by
  have h := suzukiDF6D4FixedGridShard231Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard231OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 532)) at h
  exact h

theorem suzukiDF6D4FixedGridShard231OddFull_eq_live :
    suzukiDF6D4FixedGridShard231OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 532) := by
  have h := suzukiDF6D4FixedGridShard231Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard231OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 532)) at h
  exact h

def suzukiDF6D4FixedGridShard231OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard231OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard231OddDotSoundness i.val
        suzukiDF6D4FixedGridShard231OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard231OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard231OddResidualData =
      suzukiDF6D4FixedGridShard231OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard231Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard231OddResidualData =
    suzukiDF6D4FixedGridShard231OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard231OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard231OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 532 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 532) := by
    rw [suzukiDF6D4FixedGridShard231OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 532
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231OddDotSoundness i
          suzukiDF6D4FixedGridShard231OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 532) := by
    simpa [suzukiDF6D4FixedGridShard231OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard231OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 532) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard231OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 532) := by
    rw [suzukiDF6D4FixedGridShard231OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 532
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard231OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard231OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard231OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard231OddDotSoundness i
            suzukiDF6D4FixedGridShard231OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard231OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
