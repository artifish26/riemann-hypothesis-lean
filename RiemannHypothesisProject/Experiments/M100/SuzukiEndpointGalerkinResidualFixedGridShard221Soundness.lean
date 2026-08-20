import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard221Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard221Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard221EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard221EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 221 k) := by
  have h := suzukiDF6D4FixedGridShard221Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard221EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 221 k)) at h
  exact h

def suzukiDF6D4FixedGridShard221EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard221EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard221EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard221EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard221EvenComparisonData)

theorem suzukiDF6D4FixedGridShard221EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard221EvenSolveData =
      suzukiDF6D4FixedGridShard221EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard221Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard221EvenSolveData =
    suzukiDF6D4FixedGridShard221EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard221EvenCross_eq_live :
    suzukiDF6D4FixedGridShard221EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 221) := by
  have h := suzukiDF6D4FixedGridShard221Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard221EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 221)) at h
  exact h

theorem suzukiDF6D4FixedGridShard221EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard221EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 221 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 221 k) := by
    rw [suzukiDF6D4FixedGridShard221EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 221 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221EvenDotSoundness i
          suzukiDF6D4FixedGridShard221EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 221 k) := by
    simpa [suzukiDF6D4FixedGridShard221EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard221EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 221 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 221) := by
    rw [suzukiDF6D4FixedGridShard221EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 221)
  rw [suzukiDF6D4FixedGridShard221EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard221EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard221EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard221EvenDotSoundness i
            suzukiDF6D4FixedGridShard221EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard221EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard221OddComparison_eq_live :
    suzukiDF6D4FixedGridShard221OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 221 k) := by
  have h := suzukiDF6D4FixedGridShard221Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard221OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 221 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard221OddCross_eq_live :
    suzukiDF6D4FixedGridShard221OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 221) := by
  have h := suzukiDF6D4FixedGridShard221Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard221OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 221)) at h
  exact h

def suzukiDF6D4FixedGridShard221OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard221OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard221OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard221OddDotSoundness i.val
      suzukiDF6D4FixedGridShard221OddComparisonData)

theorem suzukiDF6D4FixedGridShard221OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard221OddSolveData =
      suzukiDF6D4FixedGridShard221OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard221Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard221OddSolveData =
    suzukiDF6D4FixedGridShard221OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard221OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard221OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 221 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 221 k) := by
    rw [suzukiDF6D4FixedGridShard221OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 221 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221OddDotSoundness i
          suzukiDF6D4FixedGridShard221OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 221 k) := by
    simpa [suzukiDF6D4FixedGridShard221OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard221OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 221 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 221) := by
    rw [suzukiDF6D4FixedGridShard221OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 221)
  rw [suzukiDF6D4FixedGridShard221OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard221OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard221OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard221OddDotSoundness i
            suzukiDF6D4FixedGridShard221OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard221OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard221EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard221EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 522) := by
  have h := suzukiDF6D4FixedGridShard221Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard221EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 522)) at h
  exact h

theorem suzukiDF6D4FixedGridShard221EvenFull_eq_live :
    suzukiDF6D4FixedGridShard221EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 522) := by
  have h := suzukiDF6D4FixedGridShard221Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard221EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 522)) at h
  exact h

def suzukiDF6D4FixedGridShard221EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard221EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard221EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard221EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard221EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard221EvenResidualData =
      suzukiDF6D4FixedGridShard221EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard221Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard221EvenResidualData =
    suzukiDF6D4FixedGridShard221EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard221EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard221EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 522 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 522) := by
    rw [suzukiDF6D4FixedGridShard221EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 522
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221EvenDotSoundness i
          suzukiDF6D4FixedGridShard221EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 522) := by
    simpa [suzukiDF6D4FixedGridShard221EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard221EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 522) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 522) := by
    rw [suzukiDF6D4FixedGridShard221EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 522
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard221EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard221EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard221EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard221EvenDotSoundness i
            suzukiDF6D4FixedGridShard221EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard221EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard221OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard221OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 522) := by
  have h := suzukiDF6D4FixedGridShard221Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard221OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 522)) at h
  exact h

theorem suzukiDF6D4FixedGridShard221OddFull_eq_live :
    suzukiDF6D4FixedGridShard221OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 522) := by
  have h := suzukiDF6D4FixedGridShard221Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard221OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 522)) at h
  exact h

def suzukiDF6D4FixedGridShard221OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard221OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard221OddDotSoundness i.val
        suzukiDF6D4FixedGridShard221OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard221OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard221OddResidualData =
      suzukiDF6D4FixedGridShard221OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard221Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard221OddResidualData =
    suzukiDF6D4FixedGridShard221OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard221OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard221OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 522 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 522) := by
    rw [suzukiDF6D4FixedGridShard221OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 522
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221OddDotSoundness i
          suzukiDF6D4FixedGridShard221OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 522) := by
    simpa [suzukiDF6D4FixedGridShard221OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard221OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 522) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard221OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 522) := by
    rw [suzukiDF6D4FixedGridShard221OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 522
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard221OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard221OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard221OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard221OddDotSoundness i
            suzukiDF6D4FixedGridShard221OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard221OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
