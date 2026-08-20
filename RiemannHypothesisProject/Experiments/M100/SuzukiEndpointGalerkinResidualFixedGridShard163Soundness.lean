import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard163Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard163Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard163EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard163EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 163 k) := by
  have h := suzukiDF6D4FixedGridShard163Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard163EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 163 k)) at h
  exact h

def suzukiDF6D4FixedGridShard163EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard163EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard163EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard163EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard163EvenComparisonData)

theorem suzukiDF6D4FixedGridShard163EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard163EvenSolveData =
      suzukiDF6D4FixedGridShard163EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard163Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard163EvenSolveData =
    suzukiDF6D4FixedGridShard163EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard163EvenCross_eq_live :
    suzukiDF6D4FixedGridShard163EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 163) := by
  have h := suzukiDF6D4FixedGridShard163Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard163EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 163)) at h
  exact h

theorem suzukiDF6D4FixedGridShard163EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard163EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 163 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 163 k) := by
    rw [suzukiDF6D4FixedGridShard163EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 163 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163EvenDotSoundness i
          suzukiDF6D4FixedGridShard163EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 163 k) := by
    simpa [suzukiDF6D4FixedGridShard163EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard163EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 163 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 163) := by
    rw [suzukiDF6D4FixedGridShard163EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 163)
  rw [suzukiDF6D4FixedGridShard163EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard163EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard163EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard163EvenDotSoundness i
            suzukiDF6D4FixedGridShard163EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard163EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard163OddComparison_eq_live :
    suzukiDF6D4FixedGridShard163OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 163 k) := by
  have h := suzukiDF6D4FixedGridShard163Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard163OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 163 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard163OddCross_eq_live :
    suzukiDF6D4FixedGridShard163OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 163) := by
  have h := suzukiDF6D4FixedGridShard163Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard163OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 163)) at h
  exact h

def suzukiDF6D4FixedGridShard163OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard163OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard163OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard163OddDotSoundness i.val
      suzukiDF6D4FixedGridShard163OddComparisonData)

theorem suzukiDF6D4FixedGridShard163OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard163OddSolveData =
      suzukiDF6D4FixedGridShard163OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard163Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard163OddSolveData =
    suzukiDF6D4FixedGridShard163OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard163OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard163OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 163 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 163 k) := by
    rw [suzukiDF6D4FixedGridShard163OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 163 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163OddDotSoundness i
          suzukiDF6D4FixedGridShard163OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 163 k) := by
    simpa [suzukiDF6D4FixedGridShard163OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard163OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 163 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 163) := by
    rw [suzukiDF6D4FixedGridShard163OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 163)
  rw [suzukiDF6D4FixedGridShard163OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard163OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard163OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard163OddDotSoundness i
            suzukiDF6D4FixedGridShard163OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard163OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard163EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard163EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 464) := by
  have h := suzukiDF6D4FixedGridShard163Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard163EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 464)) at h
  exact h

theorem suzukiDF6D4FixedGridShard163EvenFull_eq_live :
    suzukiDF6D4FixedGridShard163EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 464) := by
  have h := suzukiDF6D4FixedGridShard163Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard163EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 464)) at h
  exact h

def suzukiDF6D4FixedGridShard163EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard163EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard163EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard163EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard163EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard163EvenResidualData =
      suzukiDF6D4FixedGridShard163EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard163Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard163EvenResidualData =
    suzukiDF6D4FixedGridShard163EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard163EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard163EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 464 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 464) := by
    rw [suzukiDF6D4FixedGridShard163EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 464
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163EvenDotSoundness i
          suzukiDF6D4FixedGridShard163EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 464) := by
    simpa [suzukiDF6D4FixedGridShard163EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard163EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 464) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 464) := by
    rw [suzukiDF6D4FixedGridShard163EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 464
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard163EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard163EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard163EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard163EvenDotSoundness i
            suzukiDF6D4FixedGridShard163EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard163EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard163OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard163OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 464) := by
  have h := suzukiDF6D4FixedGridShard163Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard163OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 464)) at h
  exact h

theorem suzukiDF6D4FixedGridShard163OddFull_eq_live :
    suzukiDF6D4FixedGridShard163OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 464) := by
  have h := suzukiDF6D4FixedGridShard163Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard163OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 464)) at h
  exact h

def suzukiDF6D4FixedGridShard163OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard163OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard163OddDotSoundness i.val
        suzukiDF6D4FixedGridShard163OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard163OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard163OddResidualData =
      suzukiDF6D4FixedGridShard163OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard163Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard163OddResidualData =
    suzukiDF6D4FixedGridShard163OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard163OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard163OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 464 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 464) := by
    rw [suzukiDF6D4FixedGridShard163OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 464
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163OddDotSoundness i
          suzukiDF6D4FixedGridShard163OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 464) := by
    simpa [suzukiDF6D4FixedGridShard163OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard163OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 464) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard163OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 464) := by
    rw [suzukiDF6D4FixedGridShard163OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 464
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard163OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard163OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard163OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard163OddDotSoundness i
            suzukiDF6D4FixedGridShard163OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard163OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
