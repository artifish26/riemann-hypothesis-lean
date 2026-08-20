import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard106Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard106Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard106EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard106EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 106 k) := by
  have h := suzukiDF6D4FixedGridShard106Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard106EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 106 k)) at h
  exact h

def suzukiDF6D4FixedGridShard106EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard106EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard106EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard106EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard106EvenComparisonData)

theorem suzukiDF6D4FixedGridShard106EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard106EvenSolveData =
      suzukiDF6D4FixedGridShard106EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard106Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard106EvenSolveData =
    suzukiDF6D4FixedGridShard106EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard106EvenCross_eq_live :
    suzukiDF6D4FixedGridShard106EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 106) := by
  have h := suzukiDF6D4FixedGridShard106Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard106EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 106)) at h
  exact h

theorem suzukiDF6D4FixedGridShard106EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard106EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 106 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 106 k) := by
    rw [suzukiDF6D4FixedGridShard106EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 106 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106EvenDotSoundness i
          suzukiDF6D4FixedGridShard106EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 106 k) := by
    simpa [suzukiDF6D4FixedGridShard106EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard106EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 106 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 106) := by
    rw [suzukiDF6D4FixedGridShard106EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 106)
  rw [suzukiDF6D4FixedGridShard106EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard106EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard106EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard106EvenDotSoundness i
            suzukiDF6D4FixedGridShard106EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard106EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard106OddComparison_eq_live :
    suzukiDF6D4FixedGridShard106OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 106 k) := by
  have h := suzukiDF6D4FixedGridShard106Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard106OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 106 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard106OddCross_eq_live :
    suzukiDF6D4FixedGridShard106OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 106) := by
  have h := suzukiDF6D4FixedGridShard106Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard106OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 106)) at h
  exact h

def suzukiDF6D4FixedGridShard106OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard106OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard106OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard106OddDotSoundness i.val
      suzukiDF6D4FixedGridShard106OddComparisonData)

theorem suzukiDF6D4FixedGridShard106OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard106OddSolveData =
      suzukiDF6D4FixedGridShard106OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard106Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard106OddSolveData =
    suzukiDF6D4FixedGridShard106OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard106OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard106OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 106 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 106 k) := by
    rw [suzukiDF6D4FixedGridShard106OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 106 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106OddDotSoundness i
          suzukiDF6D4FixedGridShard106OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 106 k) := by
    simpa [suzukiDF6D4FixedGridShard106OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard106OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 106 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 106) := by
    rw [suzukiDF6D4FixedGridShard106OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 106)
  rw [suzukiDF6D4FixedGridShard106OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard106OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard106OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard106OddDotSoundness i
            suzukiDF6D4FixedGridShard106OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard106OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard106EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard106EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 407) := by
  have h := suzukiDF6D4FixedGridShard106Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard106EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 407)) at h
  exact h

theorem suzukiDF6D4FixedGridShard106EvenFull_eq_live :
    suzukiDF6D4FixedGridShard106EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 407) := by
  have h := suzukiDF6D4FixedGridShard106Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard106EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 407)) at h
  exact h

def suzukiDF6D4FixedGridShard106EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard106EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard106EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard106EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard106EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard106EvenResidualData =
      suzukiDF6D4FixedGridShard106EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard106Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard106EvenResidualData =
    suzukiDF6D4FixedGridShard106EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard106EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard106EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 407 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 407) := by
    rw [suzukiDF6D4FixedGridShard106EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 407
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106EvenDotSoundness i
          suzukiDF6D4FixedGridShard106EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 407) := by
    simpa [suzukiDF6D4FixedGridShard106EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard106EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 407) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 407) := by
    rw [suzukiDF6D4FixedGridShard106EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 407
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard106EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard106EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard106EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard106EvenDotSoundness i
            suzukiDF6D4FixedGridShard106EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard106EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard106OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard106OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 407) := by
  have h := suzukiDF6D4FixedGridShard106Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard106OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 407)) at h
  exact h

theorem suzukiDF6D4FixedGridShard106OddFull_eq_live :
    suzukiDF6D4FixedGridShard106OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 407) := by
  have h := suzukiDF6D4FixedGridShard106Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard106OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 407)) at h
  exact h

def suzukiDF6D4FixedGridShard106OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard106OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard106OddDotSoundness i.val
        suzukiDF6D4FixedGridShard106OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard106OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard106OddResidualData =
      suzukiDF6D4FixedGridShard106OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard106Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard106OddResidualData =
    suzukiDF6D4FixedGridShard106OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard106OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard106OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 407 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 407) := by
    rw [suzukiDF6D4FixedGridShard106OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 407
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106OddDotSoundness i
          suzukiDF6D4FixedGridShard106OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 407) := by
    simpa [suzukiDF6D4FixedGridShard106OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard106OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 407) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard106OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 407) := by
    rw [suzukiDF6D4FixedGridShard106OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 407
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard106OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard106OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard106OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard106OddDotSoundness i
            suzukiDF6D4FixedGridShard106OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard106OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
