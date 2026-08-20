import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard074Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard074Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard074EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard074EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 74 k) := by
  have h := suzukiDF6D4FixedGridShard074Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard074EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 74 k)) at h
  exact h

def suzukiDF6D4FixedGridShard074EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard074EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard074EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard074EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard074EvenComparisonData)

theorem suzukiDF6D4FixedGridShard074EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard074EvenSolveData =
      suzukiDF6D4FixedGridShard074EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard074Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard074EvenSolveData =
    suzukiDF6D4FixedGridShard074EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard074EvenCross_eq_live :
    suzukiDF6D4FixedGridShard074EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 74) := by
  have h := suzukiDF6D4FixedGridShard074Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard074EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 74)) at h
  exact h

theorem suzukiDF6D4FixedGridShard074EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard074EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 74 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 74 k) := by
    rw [suzukiDF6D4FixedGridShard074EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 74 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074EvenDotSoundness i
          suzukiDF6D4FixedGridShard074EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 74 k) := by
    simpa [suzukiDF6D4FixedGridShard074EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard074EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 74 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 74) := by
    rw [suzukiDF6D4FixedGridShard074EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 74)
  rw [suzukiDF6D4FixedGridShard074EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard074EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard074EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard074EvenDotSoundness i
            suzukiDF6D4FixedGridShard074EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard074EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard074OddComparison_eq_live :
    suzukiDF6D4FixedGridShard074OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 74 k) := by
  have h := suzukiDF6D4FixedGridShard074Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard074OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 74 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard074OddCross_eq_live :
    suzukiDF6D4FixedGridShard074OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 74) := by
  have h := suzukiDF6D4FixedGridShard074Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard074OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 74)) at h
  exact h

def suzukiDF6D4FixedGridShard074OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard074OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard074OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard074OddDotSoundness i.val
      suzukiDF6D4FixedGridShard074OddComparisonData)

theorem suzukiDF6D4FixedGridShard074OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard074OddSolveData =
      suzukiDF6D4FixedGridShard074OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard074Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard074OddSolveData =
    suzukiDF6D4FixedGridShard074OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard074OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard074OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 74 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 74 k) := by
    rw [suzukiDF6D4FixedGridShard074OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 74 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074OddDotSoundness i
          suzukiDF6D4FixedGridShard074OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 74 k) := by
    simpa [suzukiDF6D4FixedGridShard074OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard074OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 74 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 74) := by
    rw [suzukiDF6D4FixedGridShard074OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 74)
  rw [suzukiDF6D4FixedGridShard074OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard074OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard074OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard074OddDotSoundness i
            suzukiDF6D4FixedGridShard074OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard074OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard074EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard074EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 375) := by
  have h := suzukiDF6D4FixedGridShard074Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard074EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 375)) at h
  exact h

theorem suzukiDF6D4FixedGridShard074EvenFull_eq_live :
    suzukiDF6D4FixedGridShard074EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 375) := by
  have h := suzukiDF6D4FixedGridShard074Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard074EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 375)) at h
  exact h

def suzukiDF6D4FixedGridShard074EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard074EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard074EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard074EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard074EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard074EvenResidualData =
      suzukiDF6D4FixedGridShard074EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard074Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard074EvenResidualData =
    suzukiDF6D4FixedGridShard074EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard074EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard074EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 375 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 375) := by
    rw [suzukiDF6D4FixedGridShard074EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 375
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074EvenDotSoundness i
          suzukiDF6D4FixedGridShard074EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 375) := by
    simpa [suzukiDF6D4FixedGridShard074EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard074EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 375) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 375) := by
    rw [suzukiDF6D4FixedGridShard074EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 375
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard074EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard074EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard074EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard074EvenDotSoundness i
            suzukiDF6D4FixedGridShard074EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard074EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard074OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard074OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 375) := by
  have h := suzukiDF6D4FixedGridShard074Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard074OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 375)) at h
  exact h

theorem suzukiDF6D4FixedGridShard074OddFull_eq_live :
    suzukiDF6D4FixedGridShard074OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 375) := by
  have h := suzukiDF6D4FixedGridShard074Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard074OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 375)) at h
  exact h

def suzukiDF6D4FixedGridShard074OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard074OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard074OddDotSoundness i.val
        suzukiDF6D4FixedGridShard074OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard074OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard074OddResidualData =
      suzukiDF6D4FixedGridShard074OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard074Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard074OddResidualData =
    suzukiDF6D4FixedGridShard074OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard074OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard074OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 375 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 375) := by
    rw [suzukiDF6D4FixedGridShard074OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 375
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074OddDotSoundness i
          suzukiDF6D4FixedGridShard074OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 375) := by
    simpa [suzukiDF6D4FixedGridShard074OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard074OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 375) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard074OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 375) := by
    rw [suzukiDF6D4FixedGridShard074OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 375
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard074OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard074OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard074OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard074OddDotSoundness i
            suzukiDF6D4FixedGridShard074OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard074OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
