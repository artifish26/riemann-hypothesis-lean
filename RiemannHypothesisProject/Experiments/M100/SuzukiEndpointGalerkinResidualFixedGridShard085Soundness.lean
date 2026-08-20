import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard085Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard085Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard085EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard085EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 85 k) := by
  have h := suzukiDF6D4FixedGridShard085Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard085EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 85 k)) at h
  exact h

def suzukiDF6D4FixedGridShard085EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard085EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard085EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard085EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard085EvenComparisonData)

theorem suzukiDF6D4FixedGridShard085EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard085EvenSolveData =
      suzukiDF6D4FixedGridShard085EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard085Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard085EvenSolveData =
    suzukiDF6D4FixedGridShard085EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard085EvenCross_eq_live :
    suzukiDF6D4FixedGridShard085EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 85) := by
  have h := suzukiDF6D4FixedGridShard085Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard085EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 85)) at h
  exact h

theorem suzukiDF6D4FixedGridShard085EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard085EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 85 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 85 k) := by
    rw [suzukiDF6D4FixedGridShard085EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 85 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085EvenDotSoundness i
          suzukiDF6D4FixedGridShard085EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 85 k) := by
    simpa [suzukiDF6D4FixedGridShard085EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard085EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 85 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 85) := by
    rw [suzukiDF6D4FixedGridShard085EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 85)
  rw [suzukiDF6D4FixedGridShard085EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard085EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard085EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard085EvenDotSoundness i
            suzukiDF6D4FixedGridShard085EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard085EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard085OddComparison_eq_live :
    suzukiDF6D4FixedGridShard085OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 85 k) := by
  have h := suzukiDF6D4FixedGridShard085Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard085OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 85 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard085OddCross_eq_live :
    suzukiDF6D4FixedGridShard085OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 85) := by
  have h := suzukiDF6D4FixedGridShard085Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard085OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 85)) at h
  exact h

def suzukiDF6D4FixedGridShard085OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard085OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard085OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard085OddDotSoundness i.val
      suzukiDF6D4FixedGridShard085OddComparisonData)

theorem suzukiDF6D4FixedGridShard085OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard085OddSolveData =
      suzukiDF6D4FixedGridShard085OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard085Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard085OddSolveData =
    suzukiDF6D4FixedGridShard085OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard085OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard085OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 85 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 85 k) := by
    rw [suzukiDF6D4FixedGridShard085OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 85 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085OddDotSoundness i
          suzukiDF6D4FixedGridShard085OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 85 k) := by
    simpa [suzukiDF6D4FixedGridShard085OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard085OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 85 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 85) := by
    rw [suzukiDF6D4FixedGridShard085OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 85)
  rw [suzukiDF6D4FixedGridShard085OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard085OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard085OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard085OddDotSoundness i
            suzukiDF6D4FixedGridShard085OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard085OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard085EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard085EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 386) := by
  have h := suzukiDF6D4FixedGridShard085Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard085EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 386)) at h
  exact h

theorem suzukiDF6D4FixedGridShard085EvenFull_eq_live :
    suzukiDF6D4FixedGridShard085EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 386) := by
  have h := suzukiDF6D4FixedGridShard085Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard085EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 386)) at h
  exact h

def suzukiDF6D4FixedGridShard085EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard085EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard085EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard085EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard085EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard085EvenResidualData =
      suzukiDF6D4FixedGridShard085EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard085Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard085EvenResidualData =
    suzukiDF6D4FixedGridShard085EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard085EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard085EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 386 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 386) := by
    rw [suzukiDF6D4FixedGridShard085EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 386
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085EvenDotSoundness i
          suzukiDF6D4FixedGridShard085EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 386) := by
    simpa [suzukiDF6D4FixedGridShard085EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard085EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 386) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 386) := by
    rw [suzukiDF6D4FixedGridShard085EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 386
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard085EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard085EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard085EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard085EvenDotSoundness i
            suzukiDF6D4FixedGridShard085EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard085EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard085OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard085OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 386) := by
  have h := suzukiDF6D4FixedGridShard085Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard085OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 386)) at h
  exact h

theorem suzukiDF6D4FixedGridShard085OddFull_eq_live :
    suzukiDF6D4FixedGridShard085OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 386) := by
  have h := suzukiDF6D4FixedGridShard085Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard085OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 386)) at h
  exact h

def suzukiDF6D4FixedGridShard085OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard085OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard085OddDotSoundness i.val
        suzukiDF6D4FixedGridShard085OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard085OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard085OddResidualData =
      suzukiDF6D4FixedGridShard085OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard085Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard085OddResidualData =
    suzukiDF6D4FixedGridShard085OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard085OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard085OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 386 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 386) := by
    rw [suzukiDF6D4FixedGridShard085OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 386
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085OddDotSoundness i
          suzukiDF6D4FixedGridShard085OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 386) := by
    simpa [suzukiDF6D4FixedGridShard085OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard085OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 386) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard085OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 386) := by
    rw [suzukiDF6D4FixedGridShard085OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 386
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard085OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard085OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard085OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard085OddDotSoundness i
            suzukiDF6D4FixedGridShard085OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard085OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
