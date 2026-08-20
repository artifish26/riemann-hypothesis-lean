import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard005Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard005Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard005EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard005EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 5 k) := by
  have h := suzukiDF6D4FixedGridShard005Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard005EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 5 k)) at h
  exact h

def suzukiDF6D4FixedGridShard005EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard005EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard005EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard005EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard005EvenComparisonData)

theorem suzukiDF6D4FixedGridShard005EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard005EvenSolveData =
      suzukiDF6D4FixedGridShard005EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard005Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard005EvenSolveData =
    suzukiDF6D4FixedGridShard005EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard005EvenCross_eq_live :
    suzukiDF6D4FixedGridShard005EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 5) := by
  have h := suzukiDF6D4FixedGridShard005Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard005EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 5)) at h
  exact h

theorem suzukiDF6D4FixedGridShard005EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard005EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 5 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 5 k) := by
    rw [suzukiDF6D4FixedGridShard005EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 5 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005EvenDotSoundness i
          suzukiDF6D4FixedGridShard005EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 5 k) := by
    simpa [suzukiDF6D4FixedGridShard005EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard005EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 5 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 5) := by
    rw [suzukiDF6D4FixedGridShard005EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 5)
  rw [suzukiDF6D4FixedGridShard005EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard005EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard005EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard005EvenDotSoundness i
            suzukiDF6D4FixedGridShard005EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard005EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard005OddComparison_eq_live :
    suzukiDF6D4FixedGridShard005OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 5 k) := by
  have h := suzukiDF6D4FixedGridShard005Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard005OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 5 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard005OddCross_eq_live :
    suzukiDF6D4FixedGridShard005OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 5) := by
  have h := suzukiDF6D4FixedGridShard005Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard005OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 5)) at h
  exact h

def suzukiDF6D4FixedGridShard005OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard005OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard005OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard005OddDotSoundness i.val
      suzukiDF6D4FixedGridShard005OddComparisonData)

theorem suzukiDF6D4FixedGridShard005OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard005OddSolveData =
      suzukiDF6D4FixedGridShard005OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard005Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard005OddSolveData =
    suzukiDF6D4FixedGridShard005OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard005OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard005OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 5 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 5 k) := by
    rw [suzukiDF6D4FixedGridShard005OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 5 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005OddDotSoundness i
          suzukiDF6D4FixedGridShard005OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 5 k) := by
    simpa [suzukiDF6D4FixedGridShard005OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard005OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 5 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 5) := by
    rw [suzukiDF6D4FixedGridShard005OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 5)
  rw [suzukiDF6D4FixedGridShard005OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard005OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard005OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard005OddDotSoundness i
            suzukiDF6D4FixedGridShard005OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard005OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard005EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard005EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 306) := by
  have h := suzukiDF6D4FixedGridShard005Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard005EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 306)) at h
  exact h

theorem suzukiDF6D4FixedGridShard005EvenFull_eq_live :
    suzukiDF6D4FixedGridShard005EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 306) := by
  have h := suzukiDF6D4FixedGridShard005Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard005EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 306)) at h
  exact h

def suzukiDF6D4FixedGridShard005EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard005EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard005EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard005EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard005EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard005EvenResidualData =
      suzukiDF6D4FixedGridShard005EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard005Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard005EvenResidualData =
    suzukiDF6D4FixedGridShard005EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard005EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard005EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 306 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 306) := by
    rw [suzukiDF6D4FixedGridShard005EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 306
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005EvenDotSoundness i
          suzukiDF6D4FixedGridShard005EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 306) := by
    simpa [suzukiDF6D4FixedGridShard005EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard005EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 306) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 306) := by
    rw [suzukiDF6D4FixedGridShard005EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 306
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard005EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard005EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard005EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard005EvenDotSoundness i
            suzukiDF6D4FixedGridShard005EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard005EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard005OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard005OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 306) := by
  have h := suzukiDF6D4FixedGridShard005Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard005OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 306)) at h
  exact h

theorem suzukiDF6D4FixedGridShard005OddFull_eq_live :
    suzukiDF6D4FixedGridShard005OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 306) := by
  have h := suzukiDF6D4FixedGridShard005Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard005OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 306)) at h
  exact h

def suzukiDF6D4FixedGridShard005OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard005OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard005OddDotSoundness i.val
        suzukiDF6D4FixedGridShard005OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard005OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard005OddResidualData =
      suzukiDF6D4FixedGridShard005OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard005Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard005OddResidualData =
    suzukiDF6D4FixedGridShard005OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard005OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard005OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 306 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 306) := by
    rw [suzukiDF6D4FixedGridShard005OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 306
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005OddDotSoundness i
          suzukiDF6D4FixedGridShard005OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 306) := by
    simpa [suzukiDF6D4FixedGridShard005OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard005OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 306) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard005OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 306) := by
    rw [suzukiDF6D4FixedGridShard005OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 306
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard005OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard005OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard005OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard005OddDotSoundness i
            suzukiDF6D4FixedGridShard005OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard005OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
