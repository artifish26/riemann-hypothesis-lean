import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard149Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard149Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard149EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard149EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 149 k) := by
  have h := suzukiDF6D4FixedGridShard149Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard149EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 149 k)) at h
  exact h

def suzukiDF6D4FixedGridShard149EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard149EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard149EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard149EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard149EvenComparisonData)

theorem suzukiDF6D4FixedGridShard149EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard149EvenSolveData =
      suzukiDF6D4FixedGridShard149EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard149Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard149EvenSolveData =
    suzukiDF6D4FixedGridShard149EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard149EvenCross_eq_live :
    suzukiDF6D4FixedGridShard149EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 149) := by
  have h := suzukiDF6D4FixedGridShard149Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard149EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 149)) at h
  exact h

theorem suzukiDF6D4FixedGridShard149EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard149EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 149 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 149 k) := by
    rw [suzukiDF6D4FixedGridShard149EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 149 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149EvenDotSoundness i
          suzukiDF6D4FixedGridShard149EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 149 k) := by
    simpa [suzukiDF6D4FixedGridShard149EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard149EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 149 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 149) := by
    rw [suzukiDF6D4FixedGridShard149EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 149)
  rw [suzukiDF6D4FixedGridShard149EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard149EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard149EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard149EvenDotSoundness i
            suzukiDF6D4FixedGridShard149EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard149EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard149OddComparison_eq_live :
    suzukiDF6D4FixedGridShard149OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 149 k) := by
  have h := suzukiDF6D4FixedGridShard149Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard149OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 149 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard149OddCross_eq_live :
    suzukiDF6D4FixedGridShard149OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 149) := by
  have h := suzukiDF6D4FixedGridShard149Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard149OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 149)) at h
  exact h

def suzukiDF6D4FixedGridShard149OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard149OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard149OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard149OddDotSoundness i.val
      suzukiDF6D4FixedGridShard149OddComparisonData)

theorem suzukiDF6D4FixedGridShard149OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard149OddSolveData =
      suzukiDF6D4FixedGridShard149OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard149Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard149OddSolveData =
    suzukiDF6D4FixedGridShard149OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard149OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard149OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 149 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 149 k) := by
    rw [suzukiDF6D4FixedGridShard149OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 149 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149OddDotSoundness i
          suzukiDF6D4FixedGridShard149OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 149 k) := by
    simpa [suzukiDF6D4FixedGridShard149OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard149OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 149 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 149) := by
    rw [suzukiDF6D4FixedGridShard149OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 149)
  rw [suzukiDF6D4FixedGridShard149OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard149OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard149OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard149OddDotSoundness i
            suzukiDF6D4FixedGridShard149OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard149OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard149EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard149EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 450) := by
  have h := suzukiDF6D4FixedGridShard149Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard149EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 450)) at h
  exact h

theorem suzukiDF6D4FixedGridShard149EvenFull_eq_live :
    suzukiDF6D4FixedGridShard149EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 450) := by
  have h := suzukiDF6D4FixedGridShard149Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard149EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 450)) at h
  exact h

def suzukiDF6D4FixedGridShard149EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard149EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard149EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard149EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard149EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard149EvenResidualData =
      suzukiDF6D4FixedGridShard149EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard149Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard149EvenResidualData =
    suzukiDF6D4FixedGridShard149EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard149EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard149EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 450 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 450) := by
    rw [suzukiDF6D4FixedGridShard149EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 450
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149EvenDotSoundness i
          suzukiDF6D4FixedGridShard149EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 450) := by
    simpa [suzukiDF6D4FixedGridShard149EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard149EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 450) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 450) := by
    rw [suzukiDF6D4FixedGridShard149EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 450
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard149EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard149EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard149EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard149EvenDotSoundness i
            suzukiDF6D4FixedGridShard149EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard149EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard149OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard149OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 450) := by
  have h := suzukiDF6D4FixedGridShard149Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard149OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 450)) at h
  exact h

theorem suzukiDF6D4FixedGridShard149OddFull_eq_live :
    suzukiDF6D4FixedGridShard149OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 450) := by
  have h := suzukiDF6D4FixedGridShard149Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard149OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 450)) at h
  exact h

def suzukiDF6D4FixedGridShard149OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard149OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard149OddDotSoundness i.val
        suzukiDF6D4FixedGridShard149OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard149OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard149OddResidualData =
      suzukiDF6D4FixedGridShard149OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard149Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard149OddResidualData =
    suzukiDF6D4FixedGridShard149OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard149OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard149OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 450 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 450) := by
    rw [suzukiDF6D4FixedGridShard149OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 450
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149OddDotSoundness i
          suzukiDF6D4FixedGridShard149OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 450) := by
    simpa [suzukiDF6D4FixedGridShard149OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard149OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 450) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard149OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 450) := by
    rw [suzukiDF6D4FixedGridShard149OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 450
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard149OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard149OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard149OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard149OddDotSoundness i
            suzukiDF6D4FixedGridShard149OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard149OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
