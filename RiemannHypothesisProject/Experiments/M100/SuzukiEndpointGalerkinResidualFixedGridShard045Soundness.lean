import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard045Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard045Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard045EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard045EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 45 k) := by
  have h := suzukiDF6D4FixedGridShard045Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard045EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 45 k)) at h
  exact h

def suzukiDF6D4FixedGridShard045EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard045EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard045EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard045EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard045EvenComparisonData)

theorem suzukiDF6D4FixedGridShard045EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard045EvenSolveData =
      suzukiDF6D4FixedGridShard045EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard045Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard045EvenSolveData =
    suzukiDF6D4FixedGridShard045EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard045EvenCross_eq_live :
    suzukiDF6D4FixedGridShard045EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 45) := by
  have h := suzukiDF6D4FixedGridShard045Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard045EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 45)) at h
  exact h

theorem suzukiDF6D4FixedGridShard045EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard045EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 45 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 45 k) := by
    rw [suzukiDF6D4FixedGridShard045EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 45 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045EvenDotSoundness i
          suzukiDF6D4FixedGridShard045EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 45 k) := by
    simpa [suzukiDF6D4FixedGridShard045EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard045EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 45 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 45) := by
    rw [suzukiDF6D4FixedGridShard045EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 45)
  rw [suzukiDF6D4FixedGridShard045EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard045EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard045EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard045EvenDotSoundness i
            suzukiDF6D4FixedGridShard045EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard045EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard045OddComparison_eq_live :
    suzukiDF6D4FixedGridShard045OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 45 k) := by
  have h := suzukiDF6D4FixedGridShard045Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard045OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 45 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard045OddCross_eq_live :
    suzukiDF6D4FixedGridShard045OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 45) := by
  have h := suzukiDF6D4FixedGridShard045Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard045OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 45)) at h
  exact h

def suzukiDF6D4FixedGridShard045OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard045OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard045OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard045OddDotSoundness i.val
      suzukiDF6D4FixedGridShard045OddComparisonData)

theorem suzukiDF6D4FixedGridShard045OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard045OddSolveData =
      suzukiDF6D4FixedGridShard045OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard045Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard045OddSolveData =
    suzukiDF6D4FixedGridShard045OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard045OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard045OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 45 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 45 k) := by
    rw [suzukiDF6D4FixedGridShard045OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 45 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045OddDotSoundness i
          suzukiDF6D4FixedGridShard045OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 45 k) := by
    simpa [suzukiDF6D4FixedGridShard045OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard045OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 45 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 45) := by
    rw [suzukiDF6D4FixedGridShard045OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 45)
  rw [suzukiDF6D4FixedGridShard045OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard045OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard045OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard045OddDotSoundness i
            suzukiDF6D4FixedGridShard045OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard045OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard045EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard045EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 346) := by
  have h := suzukiDF6D4FixedGridShard045Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard045EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 346)) at h
  exact h

theorem suzukiDF6D4FixedGridShard045EvenFull_eq_live :
    suzukiDF6D4FixedGridShard045EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 346) := by
  have h := suzukiDF6D4FixedGridShard045Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard045EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 346)) at h
  exact h

def suzukiDF6D4FixedGridShard045EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard045EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard045EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard045EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard045EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard045EvenResidualData =
      suzukiDF6D4FixedGridShard045EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard045Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard045EvenResidualData =
    suzukiDF6D4FixedGridShard045EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard045EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard045EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 346 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 346) := by
    rw [suzukiDF6D4FixedGridShard045EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 346
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045EvenDotSoundness i
          suzukiDF6D4FixedGridShard045EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 346) := by
    simpa [suzukiDF6D4FixedGridShard045EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard045EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 346) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 346) := by
    rw [suzukiDF6D4FixedGridShard045EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 346
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard045EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard045EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard045EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard045EvenDotSoundness i
            suzukiDF6D4FixedGridShard045EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard045EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard045OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard045OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 346) := by
  have h := suzukiDF6D4FixedGridShard045Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard045OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 346)) at h
  exact h

theorem suzukiDF6D4FixedGridShard045OddFull_eq_live :
    suzukiDF6D4FixedGridShard045OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 346) := by
  have h := suzukiDF6D4FixedGridShard045Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard045OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 346)) at h
  exact h

def suzukiDF6D4FixedGridShard045OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard045OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard045OddDotSoundness i.val
        suzukiDF6D4FixedGridShard045OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard045OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard045OddResidualData =
      suzukiDF6D4FixedGridShard045OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard045Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard045OddResidualData =
    suzukiDF6D4FixedGridShard045OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard045OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard045OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 346 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 346) := by
    rw [suzukiDF6D4FixedGridShard045OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 346
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045OddDotSoundness i
          suzukiDF6D4FixedGridShard045OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 346) := by
    simpa [suzukiDF6D4FixedGridShard045OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard045OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 346) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard045OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 346) := by
    rw [suzukiDF6D4FixedGridShard045OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 346
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard045OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard045OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard045OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard045OddDotSoundness i
            suzukiDF6D4FixedGridShard045OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard045OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
