import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard195Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard195Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard195EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard195EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 195 k) := by
  have h := suzukiDF6D4FixedGridShard195Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard195EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 195 k)) at h
  exact h

def suzukiDF6D4FixedGridShard195EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard195EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard195EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard195EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard195EvenComparisonData)

theorem suzukiDF6D4FixedGridShard195EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard195EvenSolveData =
      suzukiDF6D4FixedGridShard195EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard195Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard195EvenSolveData =
    suzukiDF6D4FixedGridShard195EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard195EvenCross_eq_live :
    suzukiDF6D4FixedGridShard195EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 195) := by
  have h := suzukiDF6D4FixedGridShard195Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard195EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 195)) at h
  exact h

theorem suzukiDF6D4FixedGridShard195EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard195EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 195 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 195 k) := by
    rw [suzukiDF6D4FixedGridShard195EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 195 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195EvenDotSoundness i
          suzukiDF6D4FixedGridShard195EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 195 k) := by
    simpa [suzukiDF6D4FixedGridShard195EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard195EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 195 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 195) := by
    rw [suzukiDF6D4FixedGridShard195EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 195)
  rw [suzukiDF6D4FixedGridShard195EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard195EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard195EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard195EvenDotSoundness i
            suzukiDF6D4FixedGridShard195EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard195EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard195OddComparison_eq_live :
    suzukiDF6D4FixedGridShard195OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 195 k) := by
  have h := suzukiDF6D4FixedGridShard195Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard195OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 195 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard195OddCross_eq_live :
    suzukiDF6D4FixedGridShard195OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 195) := by
  have h := suzukiDF6D4FixedGridShard195Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard195OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 195)) at h
  exact h

def suzukiDF6D4FixedGridShard195OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard195OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard195OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard195OddDotSoundness i.val
      suzukiDF6D4FixedGridShard195OddComparisonData)

theorem suzukiDF6D4FixedGridShard195OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard195OddSolveData =
      suzukiDF6D4FixedGridShard195OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard195Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard195OddSolveData =
    suzukiDF6D4FixedGridShard195OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard195OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard195OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 195 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 195 k) := by
    rw [suzukiDF6D4FixedGridShard195OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 195 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195OddDotSoundness i
          suzukiDF6D4FixedGridShard195OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 195 k) := by
    simpa [suzukiDF6D4FixedGridShard195OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard195OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 195 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 195) := by
    rw [suzukiDF6D4FixedGridShard195OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 195)
  rw [suzukiDF6D4FixedGridShard195OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard195OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard195OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard195OddDotSoundness i
            suzukiDF6D4FixedGridShard195OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard195OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard195EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard195EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 496) := by
  have h := suzukiDF6D4FixedGridShard195Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard195EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 496)) at h
  exact h

theorem suzukiDF6D4FixedGridShard195EvenFull_eq_live :
    suzukiDF6D4FixedGridShard195EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 496) := by
  have h := suzukiDF6D4FixedGridShard195Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard195EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 496)) at h
  exact h

def suzukiDF6D4FixedGridShard195EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard195EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard195EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard195EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard195EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard195EvenResidualData =
      suzukiDF6D4FixedGridShard195EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard195Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard195EvenResidualData =
    suzukiDF6D4FixedGridShard195EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard195EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard195EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 496 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 496) := by
    rw [suzukiDF6D4FixedGridShard195EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 496
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195EvenDotSoundness i
          suzukiDF6D4FixedGridShard195EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 496) := by
    simpa [suzukiDF6D4FixedGridShard195EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard195EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 496) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 496) := by
    rw [suzukiDF6D4FixedGridShard195EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 496
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard195EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard195EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard195EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard195EvenDotSoundness i
            suzukiDF6D4FixedGridShard195EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard195EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard195OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard195OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 496) := by
  have h := suzukiDF6D4FixedGridShard195Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard195OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 496)) at h
  exact h

theorem suzukiDF6D4FixedGridShard195OddFull_eq_live :
    suzukiDF6D4FixedGridShard195OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 496) := by
  have h := suzukiDF6D4FixedGridShard195Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard195OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 496)) at h
  exact h

def suzukiDF6D4FixedGridShard195OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard195OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard195OddDotSoundness i.val
        suzukiDF6D4FixedGridShard195OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard195OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard195OddResidualData =
      suzukiDF6D4FixedGridShard195OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard195Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard195OddResidualData =
    suzukiDF6D4FixedGridShard195OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard195OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard195OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 496 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 496) := by
    rw [suzukiDF6D4FixedGridShard195OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 496
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195OddDotSoundness i
          suzukiDF6D4FixedGridShard195OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 496) := by
    simpa [suzukiDF6D4FixedGridShard195OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard195OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 496) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard195OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 496) := by
    rw [suzukiDF6D4FixedGridShard195OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 496
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard195OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard195OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard195OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard195OddDotSoundness i
            suzukiDF6D4FixedGridShard195OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard195OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
