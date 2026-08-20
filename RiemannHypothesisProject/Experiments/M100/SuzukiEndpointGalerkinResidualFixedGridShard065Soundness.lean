import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard065Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard065Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard065EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard065EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 65 k) := by
  have h := suzukiDF6D4FixedGridShard065Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard065EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 65 k)) at h
  exact h

def suzukiDF6D4FixedGridShard065EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard065EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard065EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard065EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard065EvenComparisonData)

theorem suzukiDF6D4FixedGridShard065EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard065EvenSolveData =
      suzukiDF6D4FixedGridShard065EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard065Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard065EvenSolveData =
    suzukiDF6D4FixedGridShard065EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard065EvenCross_eq_live :
    suzukiDF6D4FixedGridShard065EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 65) := by
  have h := suzukiDF6D4FixedGridShard065Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard065EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 65)) at h
  exact h

theorem suzukiDF6D4FixedGridShard065EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard065EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 65 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 65 k) := by
    rw [suzukiDF6D4FixedGridShard065EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 65 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065EvenDotSoundness i
          suzukiDF6D4FixedGridShard065EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 65 k) := by
    simpa [suzukiDF6D4FixedGridShard065EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard065EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 65 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 65) := by
    rw [suzukiDF6D4FixedGridShard065EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 65)
  rw [suzukiDF6D4FixedGridShard065EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard065EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard065EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard065EvenDotSoundness i
            suzukiDF6D4FixedGridShard065EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard065EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard065OddComparison_eq_live :
    suzukiDF6D4FixedGridShard065OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 65 k) := by
  have h := suzukiDF6D4FixedGridShard065Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard065OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 65 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard065OddCross_eq_live :
    suzukiDF6D4FixedGridShard065OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 65) := by
  have h := suzukiDF6D4FixedGridShard065Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard065OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 65)) at h
  exact h

def suzukiDF6D4FixedGridShard065OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard065OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard065OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard065OddDotSoundness i.val
      suzukiDF6D4FixedGridShard065OddComparisonData)

theorem suzukiDF6D4FixedGridShard065OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard065OddSolveData =
      suzukiDF6D4FixedGridShard065OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard065Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard065OddSolveData =
    suzukiDF6D4FixedGridShard065OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard065OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard065OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 65 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 65 k) := by
    rw [suzukiDF6D4FixedGridShard065OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 65 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065OddDotSoundness i
          suzukiDF6D4FixedGridShard065OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 65 k) := by
    simpa [suzukiDF6D4FixedGridShard065OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard065OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 65 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 65) := by
    rw [suzukiDF6D4FixedGridShard065OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 65)
  rw [suzukiDF6D4FixedGridShard065OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard065OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard065OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard065OddDotSoundness i
            suzukiDF6D4FixedGridShard065OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard065OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard065EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard065EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 366) := by
  have h := suzukiDF6D4FixedGridShard065Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard065EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 366)) at h
  exact h

theorem suzukiDF6D4FixedGridShard065EvenFull_eq_live :
    suzukiDF6D4FixedGridShard065EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 366) := by
  have h := suzukiDF6D4FixedGridShard065Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard065EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 366)) at h
  exact h

def suzukiDF6D4FixedGridShard065EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard065EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard065EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard065EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard065EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard065EvenResidualData =
      suzukiDF6D4FixedGridShard065EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard065Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard065EvenResidualData =
    suzukiDF6D4FixedGridShard065EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard065EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard065EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 366 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 366) := by
    rw [suzukiDF6D4FixedGridShard065EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 366
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065EvenDotSoundness i
          suzukiDF6D4FixedGridShard065EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 366) := by
    simpa [suzukiDF6D4FixedGridShard065EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard065EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 366) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 366) := by
    rw [suzukiDF6D4FixedGridShard065EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 366
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard065EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard065EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard065EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard065EvenDotSoundness i
            suzukiDF6D4FixedGridShard065EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard065EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard065OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard065OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 366) := by
  have h := suzukiDF6D4FixedGridShard065Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard065OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 366)) at h
  exact h

theorem suzukiDF6D4FixedGridShard065OddFull_eq_live :
    suzukiDF6D4FixedGridShard065OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 366) := by
  have h := suzukiDF6D4FixedGridShard065Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard065OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 366)) at h
  exact h

def suzukiDF6D4FixedGridShard065OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard065OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard065OddDotSoundness i.val
        suzukiDF6D4FixedGridShard065OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard065OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard065OddResidualData =
      suzukiDF6D4FixedGridShard065OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard065Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard065OddResidualData =
    suzukiDF6D4FixedGridShard065OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard065OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard065OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 366 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 366) := by
    rw [suzukiDF6D4FixedGridShard065OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 366
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065OddDotSoundness i
          suzukiDF6D4FixedGridShard065OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 366) := by
    simpa [suzukiDF6D4FixedGridShard065OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard065OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 366) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard065OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 366) := by
    rw [suzukiDF6D4FixedGridShard065OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 366
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard065OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard065OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard065OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard065OddDotSoundness i
            suzukiDF6D4FixedGridShard065OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard065OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
