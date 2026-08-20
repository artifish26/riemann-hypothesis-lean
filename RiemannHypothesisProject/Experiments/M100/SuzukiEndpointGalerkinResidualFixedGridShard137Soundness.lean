import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard137Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard137Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard137EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard137EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 137 k) := by
  have h := suzukiDF6D4FixedGridShard137Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard137EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 137 k)) at h
  exact h

def suzukiDF6D4FixedGridShard137EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard137EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard137EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard137EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard137EvenComparisonData)

theorem suzukiDF6D4FixedGridShard137EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard137EvenSolveData =
      suzukiDF6D4FixedGridShard137EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard137Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard137EvenSolveData =
    suzukiDF6D4FixedGridShard137EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard137EvenCross_eq_live :
    suzukiDF6D4FixedGridShard137EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 137) := by
  have h := suzukiDF6D4FixedGridShard137Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard137EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 137)) at h
  exact h

theorem suzukiDF6D4FixedGridShard137EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard137EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 137 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 137 k) := by
    rw [suzukiDF6D4FixedGridShard137EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 137 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137EvenDotSoundness i
          suzukiDF6D4FixedGridShard137EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 137 k) := by
    simpa [suzukiDF6D4FixedGridShard137EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard137EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 137 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 137) := by
    rw [suzukiDF6D4FixedGridShard137EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 137)
  rw [suzukiDF6D4FixedGridShard137EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard137EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard137EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard137EvenDotSoundness i
            suzukiDF6D4FixedGridShard137EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard137EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard137OddComparison_eq_live :
    suzukiDF6D4FixedGridShard137OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 137 k) := by
  have h := suzukiDF6D4FixedGridShard137Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard137OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 137 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard137OddCross_eq_live :
    suzukiDF6D4FixedGridShard137OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 137) := by
  have h := suzukiDF6D4FixedGridShard137Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard137OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 137)) at h
  exact h

def suzukiDF6D4FixedGridShard137OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard137OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard137OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard137OddDotSoundness i.val
      suzukiDF6D4FixedGridShard137OddComparisonData)

theorem suzukiDF6D4FixedGridShard137OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard137OddSolveData =
      suzukiDF6D4FixedGridShard137OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard137Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard137OddSolveData =
    suzukiDF6D4FixedGridShard137OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard137OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard137OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 137 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 137 k) := by
    rw [suzukiDF6D4FixedGridShard137OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 137 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137OddDotSoundness i
          suzukiDF6D4FixedGridShard137OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 137 k) := by
    simpa [suzukiDF6D4FixedGridShard137OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard137OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 137 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 137) := by
    rw [suzukiDF6D4FixedGridShard137OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 137)
  rw [suzukiDF6D4FixedGridShard137OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard137OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard137OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard137OddDotSoundness i
            suzukiDF6D4FixedGridShard137OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard137OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard137EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard137EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 438) := by
  have h := suzukiDF6D4FixedGridShard137Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard137EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 438)) at h
  exact h

theorem suzukiDF6D4FixedGridShard137EvenFull_eq_live :
    suzukiDF6D4FixedGridShard137EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 438) := by
  have h := suzukiDF6D4FixedGridShard137Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard137EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 438)) at h
  exact h

def suzukiDF6D4FixedGridShard137EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard137EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard137EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard137EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard137EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard137EvenResidualData =
      suzukiDF6D4FixedGridShard137EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard137Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard137EvenResidualData =
    suzukiDF6D4FixedGridShard137EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard137EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard137EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 438 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 438) := by
    rw [suzukiDF6D4FixedGridShard137EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 438
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137EvenDotSoundness i
          suzukiDF6D4FixedGridShard137EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 438) := by
    simpa [suzukiDF6D4FixedGridShard137EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard137EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 438) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 438) := by
    rw [suzukiDF6D4FixedGridShard137EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 438
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard137EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard137EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard137EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard137EvenDotSoundness i
            suzukiDF6D4FixedGridShard137EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard137EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard137OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard137OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 438) := by
  have h := suzukiDF6D4FixedGridShard137Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard137OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 438)) at h
  exact h

theorem suzukiDF6D4FixedGridShard137OddFull_eq_live :
    suzukiDF6D4FixedGridShard137OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 438) := by
  have h := suzukiDF6D4FixedGridShard137Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard137OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 438)) at h
  exact h

def suzukiDF6D4FixedGridShard137OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard137OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard137OddDotSoundness i.val
        suzukiDF6D4FixedGridShard137OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard137OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard137OddResidualData =
      suzukiDF6D4FixedGridShard137OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard137Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard137OddResidualData =
    suzukiDF6D4FixedGridShard137OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard137OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard137OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 438 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 438) := by
    rw [suzukiDF6D4FixedGridShard137OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 438
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137OddDotSoundness i
          suzukiDF6D4FixedGridShard137OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 438) := by
    simpa [suzukiDF6D4FixedGridShard137OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard137OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 438) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard137OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 438) := by
    rw [suzukiDF6D4FixedGridShard137OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 438
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard137OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard137OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard137OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard137OddDotSoundness i
            suzukiDF6D4FixedGridShard137OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard137OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
