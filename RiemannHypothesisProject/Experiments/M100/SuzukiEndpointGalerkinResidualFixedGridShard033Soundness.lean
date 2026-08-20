import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard033Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard033Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard033EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard033EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 33 k) := by
  have h := suzukiDF6D4FixedGridShard033Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard033EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 33 k)) at h
  exact h

def suzukiDF6D4FixedGridShard033EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard033EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard033EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard033EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard033EvenComparisonData)

theorem suzukiDF6D4FixedGridShard033EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard033EvenSolveData =
      suzukiDF6D4FixedGridShard033EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard033Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard033EvenSolveData =
    suzukiDF6D4FixedGridShard033EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard033EvenCross_eq_live :
    suzukiDF6D4FixedGridShard033EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 33) := by
  have h := suzukiDF6D4FixedGridShard033Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard033EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 33)) at h
  exact h

theorem suzukiDF6D4FixedGridShard033EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard033EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 33 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 33 k) := by
    rw [suzukiDF6D4FixedGridShard033EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 33 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033EvenDotSoundness i
          suzukiDF6D4FixedGridShard033EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 33 k) := by
    simpa [suzukiDF6D4FixedGridShard033EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard033EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 33 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 33) := by
    rw [suzukiDF6D4FixedGridShard033EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 33)
  rw [suzukiDF6D4FixedGridShard033EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard033EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard033EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard033EvenDotSoundness i
            suzukiDF6D4FixedGridShard033EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard033EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard033OddComparison_eq_live :
    suzukiDF6D4FixedGridShard033OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 33 k) := by
  have h := suzukiDF6D4FixedGridShard033Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard033OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 33 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard033OddCross_eq_live :
    suzukiDF6D4FixedGridShard033OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 33) := by
  have h := suzukiDF6D4FixedGridShard033Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard033OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 33)) at h
  exact h

def suzukiDF6D4FixedGridShard033OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard033OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard033OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard033OddDotSoundness i.val
      suzukiDF6D4FixedGridShard033OddComparisonData)

theorem suzukiDF6D4FixedGridShard033OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard033OddSolveData =
      suzukiDF6D4FixedGridShard033OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard033Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard033OddSolveData =
    suzukiDF6D4FixedGridShard033OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard033OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard033OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 33 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 33 k) := by
    rw [suzukiDF6D4FixedGridShard033OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 33 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033OddDotSoundness i
          suzukiDF6D4FixedGridShard033OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 33 k) := by
    simpa [suzukiDF6D4FixedGridShard033OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard033OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 33 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 33) := by
    rw [suzukiDF6D4FixedGridShard033OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 33)
  rw [suzukiDF6D4FixedGridShard033OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard033OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard033OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard033OddDotSoundness i
            suzukiDF6D4FixedGridShard033OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard033OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard033EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard033EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 334) := by
  have h := suzukiDF6D4FixedGridShard033Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard033EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 334)) at h
  exact h

theorem suzukiDF6D4FixedGridShard033EvenFull_eq_live :
    suzukiDF6D4FixedGridShard033EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 334) := by
  have h := suzukiDF6D4FixedGridShard033Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard033EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 334)) at h
  exact h

def suzukiDF6D4FixedGridShard033EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard033EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard033EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard033EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard033EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard033EvenResidualData =
      suzukiDF6D4FixedGridShard033EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard033Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard033EvenResidualData =
    suzukiDF6D4FixedGridShard033EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard033EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard033EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 334 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 334) := by
    rw [suzukiDF6D4FixedGridShard033EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 334
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033EvenDotSoundness i
          suzukiDF6D4FixedGridShard033EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 334) := by
    simpa [suzukiDF6D4FixedGridShard033EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard033EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 334) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 334) := by
    rw [suzukiDF6D4FixedGridShard033EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 334
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard033EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard033EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard033EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard033EvenDotSoundness i
            suzukiDF6D4FixedGridShard033EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard033EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard033OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard033OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 334) := by
  have h := suzukiDF6D4FixedGridShard033Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard033OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 334)) at h
  exact h

theorem suzukiDF6D4FixedGridShard033OddFull_eq_live :
    suzukiDF6D4FixedGridShard033OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 334) := by
  have h := suzukiDF6D4FixedGridShard033Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard033OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 334)) at h
  exact h

def suzukiDF6D4FixedGridShard033OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard033OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard033OddDotSoundness i.val
        suzukiDF6D4FixedGridShard033OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard033OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard033OddResidualData =
      suzukiDF6D4FixedGridShard033OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard033Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard033OddResidualData =
    suzukiDF6D4FixedGridShard033OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard033OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard033OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 334 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 334) := by
    rw [suzukiDF6D4FixedGridShard033OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 334
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033OddDotSoundness i
          suzukiDF6D4FixedGridShard033OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 334) := by
    simpa [suzukiDF6D4FixedGridShard033OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard033OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 334) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard033OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 334) := by
    rw [suzukiDF6D4FixedGridShard033OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 334
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard033OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard033OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard033OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard033OddDotSoundness i
            suzukiDF6D4FixedGridShard033OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard033OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
