import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard178Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard178Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard178EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard178EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 178 k) := by
  have h := suzukiDF6D4FixedGridShard178Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard178EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 178 k)) at h
  exact h

def suzukiDF6D4FixedGridShard178EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard178EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard178EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard178EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard178EvenComparisonData)

theorem suzukiDF6D4FixedGridShard178EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard178EvenSolveData =
      suzukiDF6D4FixedGridShard178EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard178Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard178EvenSolveData =
    suzukiDF6D4FixedGridShard178EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard178EvenCross_eq_live :
    suzukiDF6D4FixedGridShard178EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 178) := by
  have h := suzukiDF6D4FixedGridShard178Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard178EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 178)) at h
  exact h

theorem suzukiDF6D4FixedGridShard178EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard178EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 178 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 178 k) := by
    rw [suzukiDF6D4FixedGridShard178EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 178 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178EvenDotSoundness i
          suzukiDF6D4FixedGridShard178EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 178 k) := by
    simpa [suzukiDF6D4FixedGridShard178EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard178EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 178 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 178) := by
    rw [suzukiDF6D4FixedGridShard178EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 178)
  rw [suzukiDF6D4FixedGridShard178EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard178EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard178EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard178EvenDotSoundness i
            suzukiDF6D4FixedGridShard178EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard178EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard178OddComparison_eq_live :
    suzukiDF6D4FixedGridShard178OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 178 k) := by
  have h := suzukiDF6D4FixedGridShard178Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard178OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 178 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard178OddCross_eq_live :
    suzukiDF6D4FixedGridShard178OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 178) := by
  have h := suzukiDF6D4FixedGridShard178Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard178OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 178)) at h
  exact h

def suzukiDF6D4FixedGridShard178OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard178OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard178OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard178OddDotSoundness i.val
      suzukiDF6D4FixedGridShard178OddComparisonData)

theorem suzukiDF6D4FixedGridShard178OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard178OddSolveData =
      suzukiDF6D4FixedGridShard178OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard178Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard178OddSolveData =
    suzukiDF6D4FixedGridShard178OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard178OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard178OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 178 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 178 k) := by
    rw [suzukiDF6D4FixedGridShard178OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 178 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178OddDotSoundness i
          suzukiDF6D4FixedGridShard178OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 178 k) := by
    simpa [suzukiDF6D4FixedGridShard178OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard178OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 178 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 178) := by
    rw [suzukiDF6D4FixedGridShard178OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 178)
  rw [suzukiDF6D4FixedGridShard178OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard178OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard178OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard178OddDotSoundness i
            suzukiDF6D4FixedGridShard178OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard178OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard178EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard178EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 479) := by
  have h := suzukiDF6D4FixedGridShard178Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard178EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 479)) at h
  exact h

theorem suzukiDF6D4FixedGridShard178EvenFull_eq_live :
    suzukiDF6D4FixedGridShard178EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 479) := by
  have h := suzukiDF6D4FixedGridShard178Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard178EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 479)) at h
  exact h

def suzukiDF6D4FixedGridShard178EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard178EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard178EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard178EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard178EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard178EvenResidualData =
      suzukiDF6D4FixedGridShard178EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard178Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard178EvenResidualData =
    suzukiDF6D4FixedGridShard178EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard178EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard178EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 479 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 479) := by
    rw [suzukiDF6D4FixedGridShard178EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 479
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178EvenDotSoundness i
          suzukiDF6D4FixedGridShard178EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 479) := by
    simpa [suzukiDF6D4FixedGridShard178EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard178EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 479) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 479) := by
    rw [suzukiDF6D4FixedGridShard178EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 479
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard178EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard178EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard178EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard178EvenDotSoundness i
            suzukiDF6D4FixedGridShard178EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard178EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard178OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard178OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 479) := by
  have h := suzukiDF6D4FixedGridShard178Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard178OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 479)) at h
  exact h

theorem suzukiDF6D4FixedGridShard178OddFull_eq_live :
    suzukiDF6D4FixedGridShard178OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 479) := by
  have h := suzukiDF6D4FixedGridShard178Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard178OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 479)) at h
  exact h

def suzukiDF6D4FixedGridShard178OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard178OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard178OddDotSoundness i.val
        suzukiDF6D4FixedGridShard178OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard178OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard178OddResidualData =
      suzukiDF6D4FixedGridShard178OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard178Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard178OddResidualData =
    suzukiDF6D4FixedGridShard178OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard178OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard178OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 479 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 479) := by
    rw [suzukiDF6D4FixedGridShard178OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 479
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178OddDotSoundness i
          suzukiDF6D4FixedGridShard178OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 479) := by
    simpa [suzukiDF6D4FixedGridShard178OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard178OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 479) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard178OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 479) := by
    rw [suzukiDF6D4FixedGridShard178OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 479
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard178OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard178OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard178OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard178OddDotSoundness i
            suzukiDF6D4FixedGridShard178OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard178OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
