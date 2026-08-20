import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard222Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard222Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard222EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard222EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 222 k) := by
  have h := suzukiDF6D4FixedGridShard222Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard222EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 222 k)) at h
  exact h

def suzukiDF6D4FixedGridShard222EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard222EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard222EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard222EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard222EvenComparisonData)

theorem suzukiDF6D4FixedGridShard222EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard222EvenSolveData =
      suzukiDF6D4FixedGridShard222EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard222Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard222EvenSolveData =
    suzukiDF6D4FixedGridShard222EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard222EvenCross_eq_live :
    suzukiDF6D4FixedGridShard222EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 222) := by
  have h := suzukiDF6D4FixedGridShard222Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard222EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 222)) at h
  exact h

theorem suzukiDF6D4FixedGridShard222EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard222EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 222 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 222 k) := by
    rw [suzukiDF6D4FixedGridShard222EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 222 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222EvenDotSoundness i
          suzukiDF6D4FixedGridShard222EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 222 k) := by
    simpa [suzukiDF6D4FixedGridShard222EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard222EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 222 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 222) := by
    rw [suzukiDF6D4FixedGridShard222EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 222)
  rw [suzukiDF6D4FixedGridShard222EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard222EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard222EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard222EvenDotSoundness i
            suzukiDF6D4FixedGridShard222EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard222EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard222OddComparison_eq_live :
    suzukiDF6D4FixedGridShard222OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 222 k) := by
  have h := suzukiDF6D4FixedGridShard222Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard222OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 222 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard222OddCross_eq_live :
    suzukiDF6D4FixedGridShard222OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 222) := by
  have h := suzukiDF6D4FixedGridShard222Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard222OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 222)) at h
  exact h

def suzukiDF6D4FixedGridShard222OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard222OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard222OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard222OddDotSoundness i.val
      suzukiDF6D4FixedGridShard222OddComparisonData)

theorem suzukiDF6D4FixedGridShard222OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard222OddSolveData =
      suzukiDF6D4FixedGridShard222OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard222Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard222OddSolveData =
    suzukiDF6D4FixedGridShard222OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard222OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard222OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 222 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 222 k) := by
    rw [suzukiDF6D4FixedGridShard222OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 222 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222OddDotSoundness i
          suzukiDF6D4FixedGridShard222OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 222 k) := by
    simpa [suzukiDF6D4FixedGridShard222OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard222OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 222 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 222) := by
    rw [suzukiDF6D4FixedGridShard222OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 222)
  rw [suzukiDF6D4FixedGridShard222OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard222OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard222OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard222OddDotSoundness i
            suzukiDF6D4FixedGridShard222OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard222OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard222EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard222EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 523) := by
  have h := suzukiDF6D4FixedGridShard222Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard222EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 523)) at h
  exact h

theorem suzukiDF6D4FixedGridShard222EvenFull_eq_live :
    suzukiDF6D4FixedGridShard222EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 523) := by
  have h := suzukiDF6D4FixedGridShard222Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard222EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 523)) at h
  exact h

def suzukiDF6D4FixedGridShard222EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard222EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard222EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard222EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard222EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard222EvenResidualData =
      suzukiDF6D4FixedGridShard222EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard222Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard222EvenResidualData =
    suzukiDF6D4FixedGridShard222EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard222EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard222EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 523 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 523) := by
    rw [suzukiDF6D4FixedGridShard222EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 523
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222EvenDotSoundness i
          suzukiDF6D4FixedGridShard222EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 523) := by
    simpa [suzukiDF6D4FixedGridShard222EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard222EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 523) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 523) := by
    rw [suzukiDF6D4FixedGridShard222EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 523
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard222EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard222EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard222EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard222EvenDotSoundness i
            suzukiDF6D4FixedGridShard222EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard222EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard222OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard222OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 523) := by
  have h := suzukiDF6D4FixedGridShard222Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard222OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 523)) at h
  exact h

theorem suzukiDF6D4FixedGridShard222OddFull_eq_live :
    suzukiDF6D4FixedGridShard222OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 523) := by
  have h := suzukiDF6D4FixedGridShard222Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard222OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 523)) at h
  exact h

def suzukiDF6D4FixedGridShard222OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard222OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard222OddDotSoundness i.val
        suzukiDF6D4FixedGridShard222OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard222OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard222OddResidualData =
      suzukiDF6D4FixedGridShard222OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard222Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard222OddResidualData =
    suzukiDF6D4FixedGridShard222OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard222OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard222OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 523 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 523) := by
    rw [suzukiDF6D4FixedGridShard222OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 523
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222OddDotSoundness i
          suzukiDF6D4FixedGridShard222OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 523) := by
    simpa [suzukiDF6D4FixedGridShard222OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard222OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 523) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard222OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 523) := by
    rw [suzukiDF6D4FixedGridShard222OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 523
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard222OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard222OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard222OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard222OddDotSoundness i
            suzukiDF6D4FixedGridShard222OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard222OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
