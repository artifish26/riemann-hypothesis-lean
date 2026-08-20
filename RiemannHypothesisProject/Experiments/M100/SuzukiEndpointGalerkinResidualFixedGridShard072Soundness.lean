import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard072Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard072Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard072EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard072EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 72 k) := by
  have h := suzukiDF6D4FixedGridShard072Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard072EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 72 k)) at h
  exact h

def suzukiDF6D4FixedGridShard072EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard072EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard072EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard072EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard072EvenComparisonData)

theorem suzukiDF6D4FixedGridShard072EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard072EvenSolveData =
      suzukiDF6D4FixedGridShard072EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard072Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard072EvenSolveData =
    suzukiDF6D4FixedGridShard072EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard072EvenCross_eq_live :
    suzukiDF6D4FixedGridShard072EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 72) := by
  have h := suzukiDF6D4FixedGridShard072Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard072EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 72)) at h
  exact h

theorem suzukiDF6D4FixedGridShard072EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard072EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 72 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 72 k) := by
    rw [suzukiDF6D4FixedGridShard072EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 72 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072EvenDotSoundness i
          suzukiDF6D4FixedGridShard072EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 72 k) := by
    simpa [suzukiDF6D4FixedGridShard072EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard072EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 72 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 72) := by
    rw [suzukiDF6D4FixedGridShard072EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 72)
  rw [suzukiDF6D4FixedGridShard072EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard072EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard072EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard072EvenDotSoundness i
            suzukiDF6D4FixedGridShard072EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard072EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard072OddComparison_eq_live :
    suzukiDF6D4FixedGridShard072OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 72 k) := by
  have h := suzukiDF6D4FixedGridShard072Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard072OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 72 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard072OddCross_eq_live :
    suzukiDF6D4FixedGridShard072OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 72) := by
  have h := suzukiDF6D4FixedGridShard072Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard072OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 72)) at h
  exact h

def suzukiDF6D4FixedGridShard072OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard072OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard072OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard072OddDotSoundness i.val
      suzukiDF6D4FixedGridShard072OddComparisonData)

theorem suzukiDF6D4FixedGridShard072OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard072OddSolveData =
      suzukiDF6D4FixedGridShard072OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard072Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard072OddSolveData =
    suzukiDF6D4FixedGridShard072OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard072OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard072OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 72 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 72 k) := by
    rw [suzukiDF6D4FixedGridShard072OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 72 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072OddDotSoundness i
          suzukiDF6D4FixedGridShard072OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 72 k) := by
    simpa [suzukiDF6D4FixedGridShard072OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard072OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 72 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 72) := by
    rw [suzukiDF6D4FixedGridShard072OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 72)
  rw [suzukiDF6D4FixedGridShard072OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard072OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard072OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard072OddDotSoundness i
            suzukiDF6D4FixedGridShard072OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard072OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard072EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard072EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 373) := by
  have h := suzukiDF6D4FixedGridShard072Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard072EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 373)) at h
  exact h

theorem suzukiDF6D4FixedGridShard072EvenFull_eq_live :
    suzukiDF6D4FixedGridShard072EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 373) := by
  have h := suzukiDF6D4FixedGridShard072Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard072EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 373)) at h
  exact h

def suzukiDF6D4FixedGridShard072EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard072EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard072EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard072EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard072EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard072EvenResidualData =
      suzukiDF6D4FixedGridShard072EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard072Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard072EvenResidualData =
    suzukiDF6D4FixedGridShard072EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard072EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard072EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 373 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 373) := by
    rw [suzukiDF6D4FixedGridShard072EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 373
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072EvenDotSoundness i
          suzukiDF6D4FixedGridShard072EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 373) := by
    simpa [suzukiDF6D4FixedGridShard072EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard072EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 373) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 373) := by
    rw [suzukiDF6D4FixedGridShard072EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 373
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard072EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard072EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard072EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard072EvenDotSoundness i
            suzukiDF6D4FixedGridShard072EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard072EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard072OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard072OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 373) := by
  have h := suzukiDF6D4FixedGridShard072Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard072OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 373)) at h
  exact h

theorem suzukiDF6D4FixedGridShard072OddFull_eq_live :
    suzukiDF6D4FixedGridShard072OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 373) := by
  have h := suzukiDF6D4FixedGridShard072Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard072OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 373)) at h
  exact h

def suzukiDF6D4FixedGridShard072OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard072OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard072OddDotSoundness i.val
        suzukiDF6D4FixedGridShard072OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard072OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard072OddResidualData =
      suzukiDF6D4FixedGridShard072OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard072Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard072OddResidualData =
    suzukiDF6D4FixedGridShard072OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard072OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard072OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 373 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 373) := by
    rw [suzukiDF6D4FixedGridShard072OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 373
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072OddDotSoundness i
          suzukiDF6D4FixedGridShard072OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 373) := by
    simpa [suzukiDF6D4FixedGridShard072OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard072OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 373) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard072OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 373) := by
    rw [suzukiDF6D4FixedGridShard072OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 373
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard072OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard072OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard072OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard072OddDotSoundness i
            suzukiDF6D4FixedGridShard072OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard072OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
