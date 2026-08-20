import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard087Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard087Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard087EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard087EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 87 k) := by
  have h := suzukiDF6D4FixedGridShard087Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard087EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 87 k)) at h
  exact h

def suzukiDF6D4FixedGridShard087EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard087EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard087EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard087EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard087EvenComparisonData)

theorem suzukiDF6D4FixedGridShard087EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard087EvenSolveData =
      suzukiDF6D4FixedGridShard087EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard087Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard087EvenSolveData =
    suzukiDF6D4FixedGridShard087EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard087EvenCross_eq_live :
    suzukiDF6D4FixedGridShard087EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 87) := by
  have h := suzukiDF6D4FixedGridShard087Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard087EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 87)) at h
  exact h

theorem suzukiDF6D4FixedGridShard087EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard087EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 87 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 87 k) := by
    rw [suzukiDF6D4FixedGridShard087EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 87 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087EvenDotSoundness i
          suzukiDF6D4FixedGridShard087EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 87 k) := by
    simpa [suzukiDF6D4FixedGridShard087EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard087EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 87 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 87) := by
    rw [suzukiDF6D4FixedGridShard087EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 87)
  rw [suzukiDF6D4FixedGridShard087EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard087EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard087EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard087EvenDotSoundness i
            suzukiDF6D4FixedGridShard087EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard087EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard087OddComparison_eq_live :
    suzukiDF6D4FixedGridShard087OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 87 k) := by
  have h := suzukiDF6D4FixedGridShard087Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard087OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 87 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard087OddCross_eq_live :
    suzukiDF6D4FixedGridShard087OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 87) := by
  have h := suzukiDF6D4FixedGridShard087Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard087OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 87)) at h
  exact h

def suzukiDF6D4FixedGridShard087OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard087OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard087OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard087OddDotSoundness i.val
      suzukiDF6D4FixedGridShard087OddComparisonData)

theorem suzukiDF6D4FixedGridShard087OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard087OddSolveData =
      suzukiDF6D4FixedGridShard087OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard087Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard087OddSolveData =
    suzukiDF6D4FixedGridShard087OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard087OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard087OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 87 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 87 k) := by
    rw [suzukiDF6D4FixedGridShard087OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 87 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087OddDotSoundness i
          suzukiDF6D4FixedGridShard087OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 87 k) := by
    simpa [suzukiDF6D4FixedGridShard087OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard087OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 87 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 87) := by
    rw [suzukiDF6D4FixedGridShard087OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 87)
  rw [suzukiDF6D4FixedGridShard087OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard087OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard087OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard087OddDotSoundness i
            suzukiDF6D4FixedGridShard087OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard087OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard087EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard087EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 388) := by
  have h := suzukiDF6D4FixedGridShard087Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard087EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 388)) at h
  exact h

theorem suzukiDF6D4FixedGridShard087EvenFull_eq_live :
    suzukiDF6D4FixedGridShard087EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 388) := by
  have h := suzukiDF6D4FixedGridShard087Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard087EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 388)) at h
  exact h

def suzukiDF6D4FixedGridShard087EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard087EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard087EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard087EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard087EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard087EvenResidualData =
      suzukiDF6D4FixedGridShard087EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard087Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard087EvenResidualData =
    suzukiDF6D4FixedGridShard087EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard087EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard087EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 388 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 388) := by
    rw [suzukiDF6D4FixedGridShard087EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 388
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087EvenDotSoundness i
          suzukiDF6D4FixedGridShard087EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 388) := by
    simpa [suzukiDF6D4FixedGridShard087EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard087EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 388) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 388) := by
    rw [suzukiDF6D4FixedGridShard087EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 388
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard087EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard087EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard087EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard087EvenDotSoundness i
            suzukiDF6D4FixedGridShard087EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard087EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard087OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard087OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 388) := by
  have h := suzukiDF6D4FixedGridShard087Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard087OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 388)) at h
  exact h

theorem suzukiDF6D4FixedGridShard087OddFull_eq_live :
    suzukiDF6D4FixedGridShard087OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 388) := by
  have h := suzukiDF6D4FixedGridShard087Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard087OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 388)) at h
  exact h

def suzukiDF6D4FixedGridShard087OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard087OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard087OddDotSoundness i.val
        suzukiDF6D4FixedGridShard087OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard087OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard087OddResidualData =
      suzukiDF6D4FixedGridShard087OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard087Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard087OddResidualData =
    suzukiDF6D4FixedGridShard087OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard087OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard087OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 388 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 388) := by
    rw [suzukiDF6D4FixedGridShard087OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 388
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087OddDotSoundness i
          suzukiDF6D4FixedGridShard087OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 388) := by
    simpa [suzukiDF6D4FixedGridShard087OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard087OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 388) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard087OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 388) := by
    rw [suzukiDF6D4FixedGridShard087OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 388
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard087OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard087OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard087OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard087OddDotSoundness i
            suzukiDF6D4FixedGridShard087OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard087OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
