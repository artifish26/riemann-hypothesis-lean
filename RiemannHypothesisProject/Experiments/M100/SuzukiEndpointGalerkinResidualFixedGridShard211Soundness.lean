import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard211Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard211Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard211EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard211EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 211 k) := by
  have h := suzukiDF6D4FixedGridShard211Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard211EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 211 k)) at h
  exact h

def suzukiDF6D4FixedGridShard211EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard211EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard211EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard211EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard211EvenComparisonData)

theorem suzukiDF6D4FixedGridShard211EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard211EvenSolveData =
      suzukiDF6D4FixedGridShard211EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard211Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard211EvenSolveData =
    suzukiDF6D4FixedGridShard211EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard211EvenCross_eq_live :
    suzukiDF6D4FixedGridShard211EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 211) := by
  have h := suzukiDF6D4FixedGridShard211Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard211EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 211)) at h
  exact h

theorem suzukiDF6D4FixedGridShard211EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard211EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 211 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 211 k) := by
    rw [suzukiDF6D4FixedGridShard211EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 211 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211EvenDotSoundness i
          suzukiDF6D4FixedGridShard211EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 211 k) := by
    simpa [suzukiDF6D4FixedGridShard211EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard211EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 211 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 211) := by
    rw [suzukiDF6D4FixedGridShard211EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 211)
  rw [suzukiDF6D4FixedGridShard211EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard211EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard211EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard211EvenDotSoundness i
            suzukiDF6D4FixedGridShard211EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard211EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard211OddComparison_eq_live :
    suzukiDF6D4FixedGridShard211OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 211 k) := by
  have h := suzukiDF6D4FixedGridShard211Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard211OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 211 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard211OddCross_eq_live :
    suzukiDF6D4FixedGridShard211OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 211) := by
  have h := suzukiDF6D4FixedGridShard211Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard211OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 211)) at h
  exact h

def suzukiDF6D4FixedGridShard211OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard211OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard211OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard211OddDotSoundness i.val
      suzukiDF6D4FixedGridShard211OddComparisonData)

theorem suzukiDF6D4FixedGridShard211OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard211OddSolveData =
      suzukiDF6D4FixedGridShard211OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard211Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard211OddSolveData =
    suzukiDF6D4FixedGridShard211OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard211OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard211OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 211 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 211 k) := by
    rw [suzukiDF6D4FixedGridShard211OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 211 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211OddDotSoundness i
          suzukiDF6D4FixedGridShard211OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 211 k) := by
    simpa [suzukiDF6D4FixedGridShard211OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard211OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 211 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 211) := by
    rw [suzukiDF6D4FixedGridShard211OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 211)
  rw [suzukiDF6D4FixedGridShard211OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard211OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard211OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard211OddDotSoundness i
            suzukiDF6D4FixedGridShard211OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard211OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard211EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard211EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 512) := by
  have h := suzukiDF6D4FixedGridShard211Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard211EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 512)) at h
  exact h

theorem suzukiDF6D4FixedGridShard211EvenFull_eq_live :
    suzukiDF6D4FixedGridShard211EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 512) := by
  have h := suzukiDF6D4FixedGridShard211Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard211EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 512)) at h
  exact h

def suzukiDF6D4FixedGridShard211EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard211EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard211EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard211EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard211EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard211EvenResidualData =
      suzukiDF6D4FixedGridShard211EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard211Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard211EvenResidualData =
    suzukiDF6D4FixedGridShard211EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard211EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard211EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 512 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 512) := by
    rw [suzukiDF6D4FixedGridShard211EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 512
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211EvenDotSoundness i
          suzukiDF6D4FixedGridShard211EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 512) := by
    simpa [suzukiDF6D4FixedGridShard211EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard211EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 512) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 512) := by
    rw [suzukiDF6D4FixedGridShard211EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 512
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard211EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard211EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard211EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard211EvenDotSoundness i
            suzukiDF6D4FixedGridShard211EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard211EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard211OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard211OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 512) := by
  have h := suzukiDF6D4FixedGridShard211Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard211OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 512)) at h
  exact h

theorem suzukiDF6D4FixedGridShard211OddFull_eq_live :
    suzukiDF6D4FixedGridShard211OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 512) := by
  have h := suzukiDF6D4FixedGridShard211Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard211OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 512)) at h
  exact h

def suzukiDF6D4FixedGridShard211OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard211OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard211OddDotSoundness i.val
        suzukiDF6D4FixedGridShard211OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard211OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard211OddResidualData =
      suzukiDF6D4FixedGridShard211OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard211Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard211OddResidualData =
    suzukiDF6D4FixedGridShard211OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard211OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard211OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 512 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 512) := by
    rw [suzukiDF6D4FixedGridShard211OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 512
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211OddDotSoundness i
          suzukiDF6D4FixedGridShard211OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 512) := by
    simpa [suzukiDF6D4FixedGridShard211OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard211OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 512) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard211OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 512) := by
    rw [suzukiDF6D4FixedGridShard211OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 512
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard211OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard211OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard211OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard211OddDotSoundness i
            suzukiDF6D4FixedGridShard211OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard211OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
