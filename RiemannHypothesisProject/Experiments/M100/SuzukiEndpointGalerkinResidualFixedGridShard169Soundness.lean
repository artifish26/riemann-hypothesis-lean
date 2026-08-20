import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard169Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard169Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard169EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard169EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 169 k) := by
  have h := suzukiDF6D4FixedGridShard169Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard169EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 169 k)) at h
  exact h

def suzukiDF6D4FixedGridShard169EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard169EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard169EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard169EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard169EvenComparisonData)

theorem suzukiDF6D4FixedGridShard169EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard169EvenSolveData =
      suzukiDF6D4FixedGridShard169EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard169Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard169EvenSolveData =
    suzukiDF6D4FixedGridShard169EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard169EvenCross_eq_live :
    suzukiDF6D4FixedGridShard169EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 169) := by
  have h := suzukiDF6D4FixedGridShard169Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard169EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 169)) at h
  exact h

theorem suzukiDF6D4FixedGridShard169EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard169EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 169 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 169 k) := by
    rw [suzukiDF6D4FixedGridShard169EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 169 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169EvenDotSoundness i
          suzukiDF6D4FixedGridShard169EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 169 k) := by
    simpa [suzukiDF6D4FixedGridShard169EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard169EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 169 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 169) := by
    rw [suzukiDF6D4FixedGridShard169EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 169)
  rw [suzukiDF6D4FixedGridShard169EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard169EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard169EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard169EvenDotSoundness i
            suzukiDF6D4FixedGridShard169EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard169EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard169OddComparison_eq_live :
    suzukiDF6D4FixedGridShard169OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 169 k) := by
  have h := suzukiDF6D4FixedGridShard169Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard169OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 169 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard169OddCross_eq_live :
    suzukiDF6D4FixedGridShard169OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 169) := by
  have h := suzukiDF6D4FixedGridShard169Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard169OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 169)) at h
  exact h

def suzukiDF6D4FixedGridShard169OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard169OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard169OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard169OddDotSoundness i.val
      suzukiDF6D4FixedGridShard169OddComparisonData)

theorem suzukiDF6D4FixedGridShard169OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard169OddSolveData =
      suzukiDF6D4FixedGridShard169OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard169Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard169OddSolveData =
    suzukiDF6D4FixedGridShard169OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard169OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard169OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 169 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 169 k) := by
    rw [suzukiDF6D4FixedGridShard169OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 169 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169OddDotSoundness i
          suzukiDF6D4FixedGridShard169OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 169 k) := by
    simpa [suzukiDF6D4FixedGridShard169OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard169OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 169 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 169) := by
    rw [suzukiDF6D4FixedGridShard169OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 169)
  rw [suzukiDF6D4FixedGridShard169OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard169OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard169OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard169OddDotSoundness i
            suzukiDF6D4FixedGridShard169OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard169OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard169EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard169EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 470) := by
  have h := suzukiDF6D4FixedGridShard169Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard169EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 470)) at h
  exact h

theorem suzukiDF6D4FixedGridShard169EvenFull_eq_live :
    suzukiDF6D4FixedGridShard169EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 470) := by
  have h := suzukiDF6D4FixedGridShard169Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard169EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 470)) at h
  exact h

def suzukiDF6D4FixedGridShard169EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard169EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard169EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard169EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard169EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard169EvenResidualData =
      suzukiDF6D4FixedGridShard169EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard169Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard169EvenResidualData =
    suzukiDF6D4FixedGridShard169EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard169EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard169EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 470 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 470) := by
    rw [suzukiDF6D4FixedGridShard169EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 470
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169EvenDotSoundness i
          suzukiDF6D4FixedGridShard169EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 470) := by
    simpa [suzukiDF6D4FixedGridShard169EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard169EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 470) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 470) := by
    rw [suzukiDF6D4FixedGridShard169EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 470
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard169EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard169EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard169EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard169EvenDotSoundness i
            suzukiDF6D4FixedGridShard169EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard169EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard169OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard169OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 470) := by
  have h := suzukiDF6D4FixedGridShard169Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard169OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 470)) at h
  exact h

theorem suzukiDF6D4FixedGridShard169OddFull_eq_live :
    suzukiDF6D4FixedGridShard169OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 470) := by
  have h := suzukiDF6D4FixedGridShard169Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard169OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 470)) at h
  exact h

def suzukiDF6D4FixedGridShard169OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard169OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard169OddDotSoundness i.val
        suzukiDF6D4FixedGridShard169OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard169OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard169OddResidualData =
      suzukiDF6D4FixedGridShard169OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard169Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard169OddResidualData =
    suzukiDF6D4FixedGridShard169OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard169OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard169OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 470 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 470) := by
    rw [suzukiDF6D4FixedGridShard169OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 470
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169OddDotSoundness i
          suzukiDF6D4FixedGridShard169OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 470) := by
    simpa [suzukiDF6D4FixedGridShard169OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard169OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 470) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard169OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 470) := by
    rw [suzukiDF6D4FixedGridShard169OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 470
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard169OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard169OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard169OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard169OddDotSoundness i
            suzukiDF6D4FixedGridShard169OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard169OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
