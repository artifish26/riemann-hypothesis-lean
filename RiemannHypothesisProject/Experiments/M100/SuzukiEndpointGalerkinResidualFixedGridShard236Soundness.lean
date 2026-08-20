import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard236Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard236Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard236EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard236EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 236 k) := by
  have h := suzukiDF6D4FixedGridShard236Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard236EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 236 k)) at h
  exact h

def suzukiDF6D4FixedGridShard236EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard236EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard236EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard236EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard236EvenComparisonData)

theorem suzukiDF6D4FixedGridShard236EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard236EvenSolveData =
      suzukiDF6D4FixedGridShard236EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard236Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard236EvenSolveData =
    suzukiDF6D4FixedGridShard236EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard236EvenCross_eq_live :
    suzukiDF6D4FixedGridShard236EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 236) := by
  have h := suzukiDF6D4FixedGridShard236Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard236EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 236)) at h
  exact h

theorem suzukiDF6D4FixedGridShard236EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard236EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 236 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 236 k) := by
    rw [suzukiDF6D4FixedGridShard236EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 236 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236EvenDotSoundness i
          suzukiDF6D4FixedGridShard236EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 236 k) := by
    simpa [suzukiDF6D4FixedGridShard236EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard236EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 236 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 236) := by
    rw [suzukiDF6D4FixedGridShard236EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 236)
  rw [suzukiDF6D4FixedGridShard236EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard236EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard236EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard236EvenDotSoundness i
            suzukiDF6D4FixedGridShard236EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard236EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard236OddComparison_eq_live :
    suzukiDF6D4FixedGridShard236OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 236 k) := by
  have h := suzukiDF6D4FixedGridShard236Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard236OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 236 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard236OddCross_eq_live :
    suzukiDF6D4FixedGridShard236OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 236) := by
  have h := suzukiDF6D4FixedGridShard236Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard236OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 236)) at h
  exact h

def suzukiDF6D4FixedGridShard236OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard236OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard236OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard236OddDotSoundness i.val
      suzukiDF6D4FixedGridShard236OddComparisonData)

theorem suzukiDF6D4FixedGridShard236OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard236OddSolveData =
      suzukiDF6D4FixedGridShard236OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard236Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard236OddSolveData =
    suzukiDF6D4FixedGridShard236OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard236OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard236OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 236 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 236 k) := by
    rw [suzukiDF6D4FixedGridShard236OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 236 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236OddDotSoundness i
          suzukiDF6D4FixedGridShard236OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 236 k) := by
    simpa [suzukiDF6D4FixedGridShard236OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard236OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 236 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 236) := by
    rw [suzukiDF6D4FixedGridShard236OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 236)
  rw [suzukiDF6D4FixedGridShard236OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard236OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard236OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard236OddDotSoundness i
            suzukiDF6D4FixedGridShard236OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard236OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard236EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard236EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 537) := by
  have h := suzukiDF6D4FixedGridShard236Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard236EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 537)) at h
  exact h

theorem suzukiDF6D4FixedGridShard236EvenFull_eq_live :
    suzukiDF6D4FixedGridShard236EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 537) := by
  have h := suzukiDF6D4FixedGridShard236Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard236EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 537)) at h
  exact h

def suzukiDF6D4FixedGridShard236EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard236EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard236EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard236EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard236EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard236EvenResidualData =
      suzukiDF6D4FixedGridShard236EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard236Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard236EvenResidualData =
    suzukiDF6D4FixedGridShard236EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard236EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard236EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 537 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 537) := by
    rw [suzukiDF6D4FixedGridShard236EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 537
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236EvenDotSoundness i
          suzukiDF6D4FixedGridShard236EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 537) := by
    simpa [suzukiDF6D4FixedGridShard236EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard236EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 537) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 537) := by
    rw [suzukiDF6D4FixedGridShard236EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 537
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard236EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard236EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard236EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard236EvenDotSoundness i
            suzukiDF6D4FixedGridShard236EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard236EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard236OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard236OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 537) := by
  have h := suzukiDF6D4FixedGridShard236Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard236OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 537)) at h
  exact h

theorem suzukiDF6D4FixedGridShard236OddFull_eq_live :
    suzukiDF6D4FixedGridShard236OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 537) := by
  have h := suzukiDF6D4FixedGridShard236Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard236OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 537)) at h
  exact h

def suzukiDF6D4FixedGridShard236OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard236OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard236OddDotSoundness i.val
        suzukiDF6D4FixedGridShard236OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard236OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard236OddResidualData =
      suzukiDF6D4FixedGridShard236OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard236Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard236OddResidualData =
    suzukiDF6D4FixedGridShard236OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard236OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard236OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 537 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 537) := by
    rw [suzukiDF6D4FixedGridShard236OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 537
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236OddDotSoundness i
          suzukiDF6D4FixedGridShard236OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 537) := by
    simpa [suzukiDF6D4FixedGridShard236OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard236OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 537) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard236OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 537) := by
    rw [suzukiDF6D4FixedGridShard236OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 537
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard236OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard236OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard236OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard236OddDotSoundness i
            suzukiDF6D4FixedGridShard236OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard236OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
