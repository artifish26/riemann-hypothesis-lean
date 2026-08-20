import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard047Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard047Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard047EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard047EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 47 k) := by
  have h := suzukiDF6D4FixedGridShard047Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard047EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 47 k)) at h
  exact h

def suzukiDF6D4FixedGridShard047EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard047EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard047EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard047EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard047EvenComparisonData)

theorem suzukiDF6D4FixedGridShard047EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard047EvenSolveData =
      suzukiDF6D4FixedGridShard047EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard047Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard047EvenSolveData =
    suzukiDF6D4FixedGridShard047EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard047EvenCross_eq_live :
    suzukiDF6D4FixedGridShard047EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 47) := by
  have h := suzukiDF6D4FixedGridShard047Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard047EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 47)) at h
  exact h

theorem suzukiDF6D4FixedGridShard047EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard047EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 47 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 47 k) := by
    rw [suzukiDF6D4FixedGridShard047EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 47 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047EvenDotSoundness i
          suzukiDF6D4FixedGridShard047EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 47 k) := by
    simpa [suzukiDF6D4FixedGridShard047EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard047EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 47 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 47) := by
    rw [suzukiDF6D4FixedGridShard047EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 47)
  rw [suzukiDF6D4FixedGridShard047EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard047EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard047EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard047EvenDotSoundness i
            suzukiDF6D4FixedGridShard047EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard047EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard047OddComparison_eq_live :
    suzukiDF6D4FixedGridShard047OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 47 k) := by
  have h := suzukiDF6D4FixedGridShard047Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard047OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 47 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard047OddCross_eq_live :
    suzukiDF6D4FixedGridShard047OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 47) := by
  have h := suzukiDF6D4FixedGridShard047Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard047OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 47)) at h
  exact h

def suzukiDF6D4FixedGridShard047OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard047OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard047OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard047OddDotSoundness i.val
      suzukiDF6D4FixedGridShard047OddComparisonData)

theorem suzukiDF6D4FixedGridShard047OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard047OddSolveData =
      suzukiDF6D4FixedGridShard047OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard047Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard047OddSolveData =
    suzukiDF6D4FixedGridShard047OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard047OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard047OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 47 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 47 k) := by
    rw [suzukiDF6D4FixedGridShard047OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 47 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047OddDotSoundness i
          suzukiDF6D4FixedGridShard047OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 47 k) := by
    simpa [suzukiDF6D4FixedGridShard047OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard047OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 47 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 47) := by
    rw [suzukiDF6D4FixedGridShard047OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 47)
  rw [suzukiDF6D4FixedGridShard047OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard047OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard047OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard047OddDotSoundness i
            suzukiDF6D4FixedGridShard047OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard047OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard047EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard047EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 348) := by
  have h := suzukiDF6D4FixedGridShard047Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard047EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 348)) at h
  exact h

theorem suzukiDF6D4FixedGridShard047EvenFull_eq_live :
    suzukiDF6D4FixedGridShard047EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 348) := by
  have h := suzukiDF6D4FixedGridShard047Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard047EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 348)) at h
  exact h

def suzukiDF6D4FixedGridShard047EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard047EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard047EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard047EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard047EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard047EvenResidualData =
      suzukiDF6D4FixedGridShard047EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard047Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard047EvenResidualData =
    suzukiDF6D4FixedGridShard047EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard047EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard047EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 348 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 348) := by
    rw [suzukiDF6D4FixedGridShard047EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 348
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047EvenDotSoundness i
          suzukiDF6D4FixedGridShard047EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 348) := by
    simpa [suzukiDF6D4FixedGridShard047EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard047EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 348) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 348) := by
    rw [suzukiDF6D4FixedGridShard047EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 348
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard047EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard047EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard047EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard047EvenDotSoundness i
            suzukiDF6D4FixedGridShard047EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard047EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard047OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard047OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 348) := by
  have h := suzukiDF6D4FixedGridShard047Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard047OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 348)) at h
  exact h

theorem suzukiDF6D4FixedGridShard047OddFull_eq_live :
    suzukiDF6D4FixedGridShard047OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 348) := by
  have h := suzukiDF6D4FixedGridShard047Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard047OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 348)) at h
  exact h

def suzukiDF6D4FixedGridShard047OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard047OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard047OddDotSoundness i.val
        suzukiDF6D4FixedGridShard047OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard047OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard047OddResidualData =
      suzukiDF6D4FixedGridShard047OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard047Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard047OddResidualData =
    suzukiDF6D4FixedGridShard047OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard047OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard047OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 348 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 348) := by
    rw [suzukiDF6D4FixedGridShard047OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 348
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047OddDotSoundness i
          suzukiDF6D4FixedGridShard047OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 348) := by
    simpa [suzukiDF6D4FixedGridShard047OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard047OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 348) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard047OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 348) := by
    rw [suzukiDF6D4FixedGridShard047OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 348
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard047OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard047OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard047OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard047OddDotSoundness i
            suzukiDF6D4FixedGridShard047OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard047OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
