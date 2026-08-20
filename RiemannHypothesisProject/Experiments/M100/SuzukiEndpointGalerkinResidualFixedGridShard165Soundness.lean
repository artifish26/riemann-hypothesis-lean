import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard165Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard165Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard165EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard165EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 165 k) := by
  have h := suzukiDF6D4FixedGridShard165Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard165EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 165 k)) at h
  exact h

def suzukiDF6D4FixedGridShard165EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard165EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard165EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard165EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard165EvenComparisonData)

theorem suzukiDF6D4FixedGridShard165EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard165EvenSolveData =
      suzukiDF6D4FixedGridShard165EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard165Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard165EvenSolveData =
    suzukiDF6D4FixedGridShard165EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard165EvenCross_eq_live :
    suzukiDF6D4FixedGridShard165EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 165) := by
  have h := suzukiDF6D4FixedGridShard165Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard165EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 165)) at h
  exact h

theorem suzukiDF6D4FixedGridShard165EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard165EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 165 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 165 k) := by
    rw [suzukiDF6D4FixedGridShard165EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 165 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165EvenDotSoundness i
          suzukiDF6D4FixedGridShard165EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 165 k) := by
    simpa [suzukiDF6D4FixedGridShard165EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard165EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 165 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 165) := by
    rw [suzukiDF6D4FixedGridShard165EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 165)
  rw [suzukiDF6D4FixedGridShard165EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard165EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard165EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard165EvenDotSoundness i
            suzukiDF6D4FixedGridShard165EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard165EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard165OddComparison_eq_live :
    suzukiDF6D4FixedGridShard165OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 165 k) := by
  have h := suzukiDF6D4FixedGridShard165Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard165OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 165 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard165OddCross_eq_live :
    suzukiDF6D4FixedGridShard165OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 165) := by
  have h := suzukiDF6D4FixedGridShard165Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard165OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 165)) at h
  exact h

def suzukiDF6D4FixedGridShard165OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard165OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard165OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard165OddDotSoundness i.val
      suzukiDF6D4FixedGridShard165OddComparisonData)

theorem suzukiDF6D4FixedGridShard165OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard165OddSolveData =
      suzukiDF6D4FixedGridShard165OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard165Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard165OddSolveData =
    suzukiDF6D4FixedGridShard165OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard165OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard165OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 165 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 165 k) := by
    rw [suzukiDF6D4FixedGridShard165OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 165 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165OddDotSoundness i
          suzukiDF6D4FixedGridShard165OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 165 k) := by
    simpa [suzukiDF6D4FixedGridShard165OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard165OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 165 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 165) := by
    rw [suzukiDF6D4FixedGridShard165OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 165)
  rw [suzukiDF6D4FixedGridShard165OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard165OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard165OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard165OddDotSoundness i
            suzukiDF6D4FixedGridShard165OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard165OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard165EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard165EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 466) := by
  have h := suzukiDF6D4FixedGridShard165Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard165EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 466)) at h
  exact h

theorem suzukiDF6D4FixedGridShard165EvenFull_eq_live :
    suzukiDF6D4FixedGridShard165EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 466) := by
  have h := suzukiDF6D4FixedGridShard165Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard165EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 466)) at h
  exact h

def suzukiDF6D4FixedGridShard165EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard165EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard165EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard165EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard165EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard165EvenResidualData =
      suzukiDF6D4FixedGridShard165EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard165Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard165EvenResidualData =
    suzukiDF6D4FixedGridShard165EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard165EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard165EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 466 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 466) := by
    rw [suzukiDF6D4FixedGridShard165EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 466
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165EvenDotSoundness i
          suzukiDF6D4FixedGridShard165EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 466) := by
    simpa [suzukiDF6D4FixedGridShard165EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard165EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 466) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 466) := by
    rw [suzukiDF6D4FixedGridShard165EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 466
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard165EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard165EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard165EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard165EvenDotSoundness i
            suzukiDF6D4FixedGridShard165EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard165EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard165OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard165OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 466) := by
  have h := suzukiDF6D4FixedGridShard165Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard165OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 466)) at h
  exact h

theorem suzukiDF6D4FixedGridShard165OddFull_eq_live :
    suzukiDF6D4FixedGridShard165OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 466) := by
  have h := suzukiDF6D4FixedGridShard165Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard165OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 466)) at h
  exact h

def suzukiDF6D4FixedGridShard165OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard165OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard165OddDotSoundness i.val
        suzukiDF6D4FixedGridShard165OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard165OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard165OddResidualData =
      suzukiDF6D4FixedGridShard165OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard165Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard165OddResidualData =
    suzukiDF6D4FixedGridShard165OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard165OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard165OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 466 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 466) := by
    rw [suzukiDF6D4FixedGridShard165OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 466
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165OddDotSoundness i
          suzukiDF6D4FixedGridShard165OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 466) := by
    simpa [suzukiDF6D4FixedGridShard165OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard165OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 466) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard165OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 466) := by
    rw [suzukiDF6D4FixedGridShard165OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 466
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard165OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard165OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard165OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard165OddDotSoundness i
            suzukiDF6D4FixedGridShard165OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard165OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
