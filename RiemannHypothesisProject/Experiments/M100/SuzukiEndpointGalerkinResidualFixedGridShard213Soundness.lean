import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard213Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard213Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard213EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard213EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 213 k) := by
  have h := suzukiDF6D4FixedGridShard213Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard213EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 213 k)) at h
  exact h

def suzukiDF6D4FixedGridShard213EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard213EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard213EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard213EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard213EvenComparisonData)

theorem suzukiDF6D4FixedGridShard213EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard213EvenSolveData =
      suzukiDF6D4FixedGridShard213EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard213Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard213EvenSolveData =
    suzukiDF6D4FixedGridShard213EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard213EvenCross_eq_live :
    suzukiDF6D4FixedGridShard213EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 213) := by
  have h := suzukiDF6D4FixedGridShard213Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard213EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 213)) at h
  exact h

theorem suzukiDF6D4FixedGridShard213EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard213EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 213 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 213 k) := by
    rw [suzukiDF6D4FixedGridShard213EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 213 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213EvenDotSoundness i
          suzukiDF6D4FixedGridShard213EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 213 k) := by
    simpa [suzukiDF6D4FixedGridShard213EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard213EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 213 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 213) := by
    rw [suzukiDF6D4FixedGridShard213EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 213)
  rw [suzukiDF6D4FixedGridShard213EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard213EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard213EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard213EvenDotSoundness i
            suzukiDF6D4FixedGridShard213EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard213EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard213OddComparison_eq_live :
    suzukiDF6D4FixedGridShard213OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 213 k) := by
  have h := suzukiDF6D4FixedGridShard213Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard213OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 213 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard213OddCross_eq_live :
    suzukiDF6D4FixedGridShard213OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 213) := by
  have h := suzukiDF6D4FixedGridShard213Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard213OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 213)) at h
  exact h

def suzukiDF6D4FixedGridShard213OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard213OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard213OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard213OddDotSoundness i.val
      suzukiDF6D4FixedGridShard213OddComparisonData)

theorem suzukiDF6D4FixedGridShard213OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard213OddSolveData =
      suzukiDF6D4FixedGridShard213OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard213Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard213OddSolveData =
    suzukiDF6D4FixedGridShard213OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard213OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard213OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 213 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 213 k) := by
    rw [suzukiDF6D4FixedGridShard213OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 213 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213OddDotSoundness i
          suzukiDF6D4FixedGridShard213OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 213 k) := by
    simpa [suzukiDF6D4FixedGridShard213OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard213OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 213 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 213) := by
    rw [suzukiDF6D4FixedGridShard213OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 213)
  rw [suzukiDF6D4FixedGridShard213OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard213OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard213OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard213OddDotSoundness i
            suzukiDF6D4FixedGridShard213OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard213OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard213EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard213EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 514) := by
  have h := suzukiDF6D4FixedGridShard213Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard213EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 514)) at h
  exact h

theorem suzukiDF6D4FixedGridShard213EvenFull_eq_live :
    suzukiDF6D4FixedGridShard213EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 514) := by
  have h := suzukiDF6D4FixedGridShard213Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard213EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 514)) at h
  exact h

def suzukiDF6D4FixedGridShard213EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard213EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard213EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard213EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard213EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard213EvenResidualData =
      suzukiDF6D4FixedGridShard213EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard213Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard213EvenResidualData =
    suzukiDF6D4FixedGridShard213EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard213EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard213EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 514 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 514) := by
    rw [suzukiDF6D4FixedGridShard213EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 514
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213EvenDotSoundness i
          suzukiDF6D4FixedGridShard213EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 514) := by
    simpa [suzukiDF6D4FixedGridShard213EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard213EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 514) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 514) := by
    rw [suzukiDF6D4FixedGridShard213EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 514
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard213EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard213EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard213EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard213EvenDotSoundness i
            suzukiDF6D4FixedGridShard213EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard213EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard213OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard213OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 514) := by
  have h := suzukiDF6D4FixedGridShard213Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard213OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 514)) at h
  exact h

theorem suzukiDF6D4FixedGridShard213OddFull_eq_live :
    suzukiDF6D4FixedGridShard213OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 514) := by
  have h := suzukiDF6D4FixedGridShard213Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard213OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 514)) at h
  exact h

def suzukiDF6D4FixedGridShard213OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard213OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard213OddDotSoundness i.val
        suzukiDF6D4FixedGridShard213OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard213OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard213OddResidualData =
      suzukiDF6D4FixedGridShard213OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard213Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard213OddResidualData =
    suzukiDF6D4FixedGridShard213OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard213OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard213OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 514 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 514) := by
    rw [suzukiDF6D4FixedGridShard213OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 514
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213OddDotSoundness i
          suzukiDF6D4FixedGridShard213OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 514) := by
    simpa [suzukiDF6D4FixedGridShard213OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard213OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 514) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard213OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 514) := by
    rw [suzukiDF6D4FixedGridShard213OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 514
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard213OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard213OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard213OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard213OddDotSoundness i
            suzukiDF6D4FixedGridShard213OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard213OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
