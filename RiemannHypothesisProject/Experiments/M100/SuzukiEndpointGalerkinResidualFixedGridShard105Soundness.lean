import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard105Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard105Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard105EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard105EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 105 k) := by
  have h := suzukiDF6D4FixedGridShard105Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard105EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 105 k)) at h
  exact h

def suzukiDF6D4FixedGridShard105EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard105EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard105EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard105EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard105EvenComparisonData)

theorem suzukiDF6D4FixedGridShard105EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard105EvenSolveData =
      suzukiDF6D4FixedGridShard105EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard105Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard105EvenSolveData =
    suzukiDF6D4FixedGridShard105EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard105EvenCross_eq_live :
    suzukiDF6D4FixedGridShard105EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 105) := by
  have h := suzukiDF6D4FixedGridShard105Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard105EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 105)) at h
  exact h

theorem suzukiDF6D4FixedGridShard105EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard105EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 105 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 105 k) := by
    rw [suzukiDF6D4FixedGridShard105EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 105 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105EvenDotSoundness i
          suzukiDF6D4FixedGridShard105EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 105 k) := by
    simpa [suzukiDF6D4FixedGridShard105EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard105EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 105 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 105) := by
    rw [suzukiDF6D4FixedGridShard105EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 105)
  rw [suzukiDF6D4FixedGridShard105EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard105EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard105EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard105EvenDotSoundness i
            suzukiDF6D4FixedGridShard105EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard105EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard105OddComparison_eq_live :
    suzukiDF6D4FixedGridShard105OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 105 k) := by
  have h := suzukiDF6D4FixedGridShard105Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard105OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 105 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard105OddCross_eq_live :
    suzukiDF6D4FixedGridShard105OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 105) := by
  have h := suzukiDF6D4FixedGridShard105Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard105OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 105)) at h
  exact h

def suzukiDF6D4FixedGridShard105OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard105OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard105OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard105OddDotSoundness i.val
      suzukiDF6D4FixedGridShard105OddComparisonData)

theorem suzukiDF6D4FixedGridShard105OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard105OddSolveData =
      suzukiDF6D4FixedGridShard105OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard105Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard105OddSolveData =
    suzukiDF6D4FixedGridShard105OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard105OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard105OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 105 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 105 k) := by
    rw [suzukiDF6D4FixedGridShard105OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 105 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105OddDotSoundness i
          suzukiDF6D4FixedGridShard105OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 105 k) := by
    simpa [suzukiDF6D4FixedGridShard105OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard105OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 105 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 105) := by
    rw [suzukiDF6D4FixedGridShard105OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 105)
  rw [suzukiDF6D4FixedGridShard105OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard105OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard105OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard105OddDotSoundness i
            suzukiDF6D4FixedGridShard105OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard105OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard105EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard105EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 406) := by
  have h := suzukiDF6D4FixedGridShard105Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard105EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 406)) at h
  exact h

theorem suzukiDF6D4FixedGridShard105EvenFull_eq_live :
    suzukiDF6D4FixedGridShard105EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 406) := by
  have h := suzukiDF6D4FixedGridShard105Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard105EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 406)) at h
  exact h

def suzukiDF6D4FixedGridShard105EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard105EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard105EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard105EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard105EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard105EvenResidualData =
      suzukiDF6D4FixedGridShard105EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard105Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard105EvenResidualData =
    suzukiDF6D4FixedGridShard105EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard105EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard105EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 406 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 406) := by
    rw [suzukiDF6D4FixedGridShard105EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 406
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105EvenDotSoundness i
          suzukiDF6D4FixedGridShard105EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 406) := by
    simpa [suzukiDF6D4FixedGridShard105EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard105EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 406) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 406) := by
    rw [suzukiDF6D4FixedGridShard105EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 406
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard105EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard105EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard105EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard105EvenDotSoundness i
            suzukiDF6D4FixedGridShard105EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard105EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard105OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard105OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 406) := by
  have h := suzukiDF6D4FixedGridShard105Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard105OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 406)) at h
  exact h

theorem suzukiDF6D4FixedGridShard105OddFull_eq_live :
    suzukiDF6D4FixedGridShard105OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 406) := by
  have h := suzukiDF6D4FixedGridShard105Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard105OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 406)) at h
  exact h

def suzukiDF6D4FixedGridShard105OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard105OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard105OddDotSoundness i.val
        suzukiDF6D4FixedGridShard105OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard105OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard105OddResidualData =
      suzukiDF6D4FixedGridShard105OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard105Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard105OddResidualData =
    suzukiDF6D4FixedGridShard105OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard105OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard105OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 406 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 406) := by
    rw [suzukiDF6D4FixedGridShard105OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 406
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105OddDotSoundness i
          suzukiDF6D4FixedGridShard105OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 406) := by
    simpa [suzukiDF6D4FixedGridShard105OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard105OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 406) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard105OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 406) := by
    rw [suzukiDF6D4FixedGridShard105OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 406
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard105OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard105OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard105OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard105OddDotSoundness i
            suzukiDF6D4FixedGridShard105OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard105OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
