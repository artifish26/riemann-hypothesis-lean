import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard113Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard113Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard113EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard113EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 113 k) := by
  have h := suzukiDF6D4FixedGridShard113Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard113EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 113 k)) at h
  exact h

def suzukiDF6D4FixedGridShard113EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard113EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard113EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard113EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard113EvenComparisonData)

theorem suzukiDF6D4FixedGridShard113EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard113EvenSolveData =
      suzukiDF6D4FixedGridShard113EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard113Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard113EvenSolveData =
    suzukiDF6D4FixedGridShard113EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard113EvenCross_eq_live :
    suzukiDF6D4FixedGridShard113EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 113) := by
  have h := suzukiDF6D4FixedGridShard113Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard113EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 113)) at h
  exact h

theorem suzukiDF6D4FixedGridShard113EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard113EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 113 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 113 k) := by
    rw [suzukiDF6D4FixedGridShard113EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 113 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113EvenDotSoundness i
          suzukiDF6D4FixedGridShard113EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 113 k) := by
    simpa [suzukiDF6D4FixedGridShard113EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard113EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 113 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 113) := by
    rw [suzukiDF6D4FixedGridShard113EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 113)
  rw [suzukiDF6D4FixedGridShard113EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard113EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard113EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard113EvenDotSoundness i
            suzukiDF6D4FixedGridShard113EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard113EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard113OddComparison_eq_live :
    suzukiDF6D4FixedGridShard113OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 113 k) := by
  have h := suzukiDF6D4FixedGridShard113Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard113OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 113 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard113OddCross_eq_live :
    suzukiDF6D4FixedGridShard113OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 113) := by
  have h := suzukiDF6D4FixedGridShard113Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard113OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 113)) at h
  exact h

def suzukiDF6D4FixedGridShard113OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard113OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard113OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard113OddDotSoundness i.val
      suzukiDF6D4FixedGridShard113OddComparisonData)

theorem suzukiDF6D4FixedGridShard113OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard113OddSolveData =
      suzukiDF6D4FixedGridShard113OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard113Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard113OddSolveData =
    suzukiDF6D4FixedGridShard113OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard113OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard113OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 113 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 113 k) := by
    rw [suzukiDF6D4FixedGridShard113OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 113 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113OddDotSoundness i
          suzukiDF6D4FixedGridShard113OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 113 k) := by
    simpa [suzukiDF6D4FixedGridShard113OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard113OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 113 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 113) := by
    rw [suzukiDF6D4FixedGridShard113OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 113)
  rw [suzukiDF6D4FixedGridShard113OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard113OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard113OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard113OddDotSoundness i
            suzukiDF6D4FixedGridShard113OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard113OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard113EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard113EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 414) := by
  have h := suzukiDF6D4FixedGridShard113Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard113EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 414)) at h
  exact h

theorem suzukiDF6D4FixedGridShard113EvenFull_eq_live :
    suzukiDF6D4FixedGridShard113EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 414) := by
  have h := suzukiDF6D4FixedGridShard113Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard113EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 414)) at h
  exact h

def suzukiDF6D4FixedGridShard113EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard113EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard113EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard113EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard113EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard113EvenResidualData =
      suzukiDF6D4FixedGridShard113EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard113Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard113EvenResidualData =
    suzukiDF6D4FixedGridShard113EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard113EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard113EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 414 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 414) := by
    rw [suzukiDF6D4FixedGridShard113EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 414
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113EvenDotSoundness i
          suzukiDF6D4FixedGridShard113EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 414) := by
    simpa [suzukiDF6D4FixedGridShard113EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard113EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 414) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 414) := by
    rw [suzukiDF6D4FixedGridShard113EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 414
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard113EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard113EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard113EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard113EvenDotSoundness i
            suzukiDF6D4FixedGridShard113EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard113EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard113OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard113OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 414) := by
  have h := suzukiDF6D4FixedGridShard113Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard113OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 414)) at h
  exact h

theorem suzukiDF6D4FixedGridShard113OddFull_eq_live :
    suzukiDF6D4FixedGridShard113OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 414) := by
  have h := suzukiDF6D4FixedGridShard113Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard113OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 414)) at h
  exact h

def suzukiDF6D4FixedGridShard113OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard113OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard113OddDotSoundness i.val
        suzukiDF6D4FixedGridShard113OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard113OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard113OddResidualData =
      suzukiDF6D4FixedGridShard113OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard113Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard113OddResidualData =
    suzukiDF6D4FixedGridShard113OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard113OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard113OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 414 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 414) := by
    rw [suzukiDF6D4FixedGridShard113OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 414
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113OddDotSoundness i
          suzukiDF6D4FixedGridShard113OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 414) := by
    simpa [suzukiDF6D4FixedGridShard113OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard113OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 414) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard113OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 414) := by
    rw [suzukiDF6D4FixedGridShard113OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 414
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard113OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard113OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard113OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard113OddDotSoundness i
            suzukiDF6D4FixedGridShard113OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard113OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
