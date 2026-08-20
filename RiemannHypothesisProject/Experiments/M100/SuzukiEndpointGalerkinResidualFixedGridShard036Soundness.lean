import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard036Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard036Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard036EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard036EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 36 k) := by
  have h := suzukiDF6D4FixedGridShard036Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard036EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 36 k)) at h
  exact h

def suzukiDF6D4FixedGridShard036EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard036EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard036EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard036EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard036EvenComparisonData)

theorem suzukiDF6D4FixedGridShard036EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard036EvenSolveData =
      suzukiDF6D4FixedGridShard036EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard036Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard036EvenSolveData =
    suzukiDF6D4FixedGridShard036EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard036EvenCross_eq_live :
    suzukiDF6D4FixedGridShard036EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 36) := by
  have h := suzukiDF6D4FixedGridShard036Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard036EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 36)) at h
  exact h

theorem suzukiDF6D4FixedGridShard036EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard036EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 36 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 36 k) := by
    rw [suzukiDF6D4FixedGridShard036EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 36 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036EvenDotSoundness i
          suzukiDF6D4FixedGridShard036EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 36 k) := by
    simpa [suzukiDF6D4FixedGridShard036EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard036EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 36 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 36) := by
    rw [suzukiDF6D4FixedGridShard036EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 36)
  rw [suzukiDF6D4FixedGridShard036EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard036EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard036EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard036EvenDotSoundness i
            suzukiDF6D4FixedGridShard036EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard036EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard036OddComparison_eq_live :
    suzukiDF6D4FixedGridShard036OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 36 k) := by
  have h := suzukiDF6D4FixedGridShard036Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard036OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 36 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard036OddCross_eq_live :
    suzukiDF6D4FixedGridShard036OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 36) := by
  have h := suzukiDF6D4FixedGridShard036Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard036OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 36)) at h
  exact h

def suzukiDF6D4FixedGridShard036OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard036OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard036OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard036OddDotSoundness i.val
      suzukiDF6D4FixedGridShard036OddComparisonData)

theorem suzukiDF6D4FixedGridShard036OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard036OddSolveData =
      suzukiDF6D4FixedGridShard036OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard036Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard036OddSolveData =
    suzukiDF6D4FixedGridShard036OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard036OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard036OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 36 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 36 k) := by
    rw [suzukiDF6D4FixedGridShard036OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 36 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036OddDotSoundness i
          suzukiDF6D4FixedGridShard036OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 36 k) := by
    simpa [suzukiDF6D4FixedGridShard036OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard036OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 36 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 36) := by
    rw [suzukiDF6D4FixedGridShard036OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 36)
  rw [suzukiDF6D4FixedGridShard036OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard036OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard036OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard036OddDotSoundness i
            suzukiDF6D4FixedGridShard036OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard036OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard036EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard036EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 337) := by
  have h := suzukiDF6D4FixedGridShard036Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard036EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 337)) at h
  exact h

theorem suzukiDF6D4FixedGridShard036EvenFull_eq_live :
    suzukiDF6D4FixedGridShard036EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 337) := by
  have h := suzukiDF6D4FixedGridShard036Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard036EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 337)) at h
  exact h

def suzukiDF6D4FixedGridShard036EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard036EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard036EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard036EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard036EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard036EvenResidualData =
      suzukiDF6D4FixedGridShard036EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard036Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard036EvenResidualData =
    suzukiDF6D4FixedGridShard036EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard036EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard036EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 337 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 337) := by
    rw [suzukiDF6D4FixedGridShard036EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 337
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036EvenDotSoundness i
          suzukiDF6D4FixedGridShard036EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 337) := by
    simpa [suzukiDF6D4FixedGridShard036EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard036EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 337) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 337) := by
    rw [suzukiDF6D4FixedGridShard036EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 337
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard036EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard036EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard036EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard036EvenDotSoundness i
            suzukiDF6D4FixedGridShard036EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard036EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard036OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard036OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 337) := by
  have h := suzukiDF6D4FixedGridShard036Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard036OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 337)) at h
  exact h

theorem suzukiDF6D4FixedGridShard036OddFull_eq_live :
    suzukiDF6D4FixedGridShard036OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 337) := by
  have h := suzukiDF6D4FixedGridShard036Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard036OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 337)) at h
  exact h

def suzukiDF6D4FixedGridShard036OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard036OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard036OddDotSoundness i.val
        suzukiDF6D4FixedGridShard036OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard036OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard036OddResidualData =
      suzukiDF6D4FixedGridShard036OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard036Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard036OddResidualData =
    suzukiDF6D4FixedGridShard036OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard036OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard036OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 337 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 337) := by
    rw [suzukiDF6D4FixedGridShard036OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 337
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036OddDotSoundness i
          suzukiDF6D4FixedGridShard036OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 337) := by
    simpa [suzukiDF6D4FixedGridShard036OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard036OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 337) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard036OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 337) := by
    rw [suzukiDF6D4FixedGridShard036OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 337
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard036OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard036OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard036OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard036OddDotSoundness i
            suzukiDF6D4FixedGridShard036OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard036OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
