import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard254Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard254Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard254EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard254EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 254 k) := by
  have h := suzukiDF6D4FixedGridShard254Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard254EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 254 k)) at h
  exact h

def suzukiDF6D4FixedGridShard254EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard254EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard254EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard254EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard254EvenComparisonData)

theorem suzukiDF6D4FixedGridShard254EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard254EvenSolveData =
      suzukiDF6D4FixedGridShard254EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard254Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard254EvenSolveData =
    suzukiDF6D4FixedGridShard254EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard254EvenCross_eq_live :
    suzukiDF6D4FixedGridShard254EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 254) := by
  have h := suzukiDF6D4FixedGridShard254Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard254EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 254)) at h
  exact h

theorem suzukiDF6D4FixedGridShard254EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard254EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 254 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 254 k) := by
    rw [suzukiDF6D4FixedGridShard254EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 254 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254EvenDotSoundness i
          suzukiDF6D4FixedGridShard254EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 254 k) := by
    simpa [suzukiDF6D4FixedGridShard254EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard254EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 254 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 254) := by
    rw [suzukiDF6D4FixedGridShard254EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 254)
  rw [suzukiDF6D4FixedGridShard254EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard254EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard254EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard254EvenDotSoundness i
            suzukiDF6D4FixedGridShard254EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard254EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard254OddComparison_eq_live :
    suzukiDF6D4FixedGridShard254OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 254 k) := by
  have h := suzukiDF6D4FixedGridShard254Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard254OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 254 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard254OddCross_eq_live :
    suzukiDF6D4FixedGridShard254OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 254) := by
  have h := suzukiDF6D4FixedGridShard254Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard254OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 254)) at h
  exact h

def suzukiDF6D4FixedGridShard254OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard254OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard254OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard254OddDotSoundness i.val
      suzukiDF6D4FixedGridShard254OddComparisonData)

theorem suzukiDF6D4FixedGridShard254OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard254OddSolveData =
      suzukiDF6D4FixedGridShard254OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard254Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard254OddSolveData =
    suzukiDF6D4FixedGridShard254OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard254OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard254OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 254 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 254 k) := by
    rw [suzukiDF6D4FixedGridShard254OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 254 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254OddDotSoundness i
          suzukiDF6D4FixedGridShard254OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 254 k) := by
    simpa [suzukiDF6D4FixedGridShard254OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard254OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 254 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 254) := by
    rw [suzukiDF6D4FixedGridShard254OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 254)
  rw [suzukiDF6D4FixedGridShard254OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard254OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard254OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard254OddDotSoundness i
            suzukiDF6D4FixedGridShard254OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard254OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard254EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard254EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 555) := by
  have h := suzukiDF6D4FixedGridShard254Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard254EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 555)) at h
  exact h

theorem suzukiDF6D4FixedGridShard254EvenFull_eq_live :
    suzukiDF6D4FixedGridShard254EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 555) := by
  have h := suzukiDF6D4FixedGridShard254Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard254EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 555)) at h
  exact h

def suzukiDF6D4FixedGridShard254EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard254EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard254EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard254EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard254EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard254EvenResidualData =
      suzukiDF6D4FixedGridShard254EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard254Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard254EvenResidualData =
    suzukiDF6D4FixedGridShard254EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard254EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard254EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 555 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 555) := by
    rw [suzukiDF6D4FixedGridShard254EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 555
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254EvenDotSoundness i
          suzukiDF6D4FixedGridShard254EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 555) := by
    simpa [suzukiDF6D4FixedGridShard254EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard254EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 555) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 555) := by
    rw [suzukiDF6D4FixedGridShard254EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 555
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard254EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard254EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard254EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard254EvenDotSoundness i
            suzukiDF6D4FixedGridShard254EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard254EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard254OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard254OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 555) := by
  have h := suzukiDF6D4FixedGridShard254Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard254OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 555)) at h
  exact h

theorem suzukiDF6D4FixedGridShard254OddFull_eq_live :
    suzukiDF6D4FixedGridShard254OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 555) := by
  have h := suzukiDF6D4FixedGridShard254Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard254OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 555)) at h
  exact h

def suzukiDF6D4FixedGridShard254OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard254OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard254OddDotSoundness i.val
        suzukiDF6D4FixedGridShard254OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard254OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard254OddResidualData =
      suzukiDF6D4FixedGridShard254OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard254Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard254OddResidualData =
    suzukiDF6D4FixedGridShard254OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard254OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard254OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 555 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 555) := by
    rw [suzukiDF6D4FixedGridShard254OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 555
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254OddDotSoundness i
          suzukiDF6D4FixedGridShard254OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 555) := by
    simpa [suzukiDF6D4FixedGridShard254OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard254OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 555) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard254OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 555) := by
    rw [suzukiDF6D4FixedGridShard254OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 555
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard254OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard254OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard254OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard254OddDotSoundness i
            suzukiDF6D4FixedGridShard254OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard254OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
