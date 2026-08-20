import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard218Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard218Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard218EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard218EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 218 k) := by
  have h := suzukiDF6D4FixedGridShard218Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard218EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 218 k)) at h
  exact h

def suzukiDF6D4FixedGridShard218EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard218EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard218EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard218EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard218EvenComparisonData)

theorem suzukiDF6D4FixedGridShard218EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard218EvenSolveData =
      suzukiDF6D4FixedGridShard218EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard218Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard218EvenSolveData =
    suzukiDF6D4FixedGridShard218EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard218EvenCross_eq_live :
    suzukiDF6D4FixedGridShard218EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 218) := by
  have h := suzukiDF6D4FixedGridShard218Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard218EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 218)) at h
  exact h

theorem suzukiDF6D4FixedGridShard218EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard218EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 218 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 218 k) := by
    rw [suzukiDF6D4FixedGridShard218EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 218 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218EvenDotSoundness i
          suzukiDF6D4FixedGridShard218EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 218 k) := by
    simpa [suzukiDF6D4FixedGridShard218EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard218EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 218 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 218) := by
    rw [suzukiDF6D4FixedGridShard218EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 218)
  rw [suzukiDF6D4FixedGridShard218EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard218EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard218EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard218EvenDotSoundness i
            suzukiDF6D4FixedGridShard218EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard218EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard218OddComparison_eq_live :
    suzukiDF6D4FixedGridShard218OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 218 k) := by
  have h := suzukiDF6D4FixedGridShard218Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard218OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 218 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard218OddCross_eq_live :
    suzukiDF6D4FixedGridShard218OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 218) := by
  have h := suzukiDF6D4FixedGridShard218Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard218OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 218)) at h
  exact h

def suzukiDF6D4FixedGridShard218OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard218OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard218OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard218OddDotSoundness i.val
      suzukiDF6D4FixedGridShard218OddComparisonData)

theorem suzukiDF6D4FixedGridShard218OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard218OddSolveData =
      suzukiDF6D4FixedGridShard218OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard218Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard218OddSolveData =
    suzukiDF6D4FixedGridShard218OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard218OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard218OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 218 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 218 k) := by
    rw [suzukiDF6D4FixedGridShard218OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 218 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218OddDotSoundness i
          suzukiDF6D4FixedGridShard218OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 218 k) := by
    simpa [suzukiDF6D4FixedGridShard218OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard218OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 218 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 218) := by
    rw [suzukiDF6D4FixedGridShard218OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 218)
  rw [suzukiDF6D4FixedGridShard218OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard218OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard218OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard218OddDotSoundness i
            suzukiDF6D4FixedGridShard218OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard218OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard218EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard218EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 519) := by
  have h := suzukiDF6D4FixedGridShard218Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard218EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 519)) at h
  exact h

theorem suzukiDF6D4FixedGridShard218EvenFull_eq_live :
    suzukiDF6D4FixedGridShard218EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 519) := by
  have h := suzukiDF6D4FixedGridShard218Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard218EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 519)) at h
  exact h

def suzukiDF6D4FixedGridShard218EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard218EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard218EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard218EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard218EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard218EvenResidualData =
      suzukiDF6D4FixedGridShard218EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard218Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard218EvenResidualData =
    suzukiDF6D4FixedGridShard218EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard218EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard218EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 519 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 519) := by
    rw [suzukiDF6D4FixedGridShard218EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 519
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218EvenDotSoundness i
          suzukiDF6D4FixedGridShard218EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 519) := by
    simpa [suzukiDF6D4FixedGridShard218EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard218EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 519) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 519) := by
    rw [suzukiDF6D4FixedGridShard218EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 519
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard218EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard218EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard218EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard218EvenDotSoundness i
            suzukiDF6D4FixedGridShard218EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard218EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard218OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard218OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 519) := by
  have h := suzukiDF6D4FixedGridShard218Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard218OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 519)) at h
  exact h

theorem suzukiDF6D4FixedGridShard218OddFull_eq_live :
    suzukiDF6D4FixedGridShard218OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 519) := by
  have h := suzukiDF6D4FixedGridShard218Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard218OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 519)) at h
  exact h

def suzukiDF6D4FixedGridShard218OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard218OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard218OddDotSoundness i.val
        suzukiDF6D4FixedGridShard218OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard218OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard218OddResidualData =
      suzukiDF6D4FixedGridShard218OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard218Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard218OddResidualData =
    suzukiDF6D4FixedGridShard218OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard218OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard218OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 519 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 519) := by
    rw [suzukiDF6D4FixedGridShard218OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 519
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218OddDotSoundness i
          suzukiDF6D4FixedGridShard218OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 519) := by
    simpa [suzukiDF6D4FixedGridShard218OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard218OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 519) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard218OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 519) := by
    rw [suzukiDF6D4FixedGridShard218OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 519
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard218OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard218OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard218OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard218OddDotSoundness i
            suzukiDF6D4FixedGridShard218OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard218OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
