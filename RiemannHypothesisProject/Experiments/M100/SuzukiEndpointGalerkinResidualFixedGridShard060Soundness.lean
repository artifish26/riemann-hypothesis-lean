import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard060Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard060Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard060EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard060EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 60 k) := by
  have h := suzukiDF6D4FixedGridShard060Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard060EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 60 k)) at h
  exact h

def suzukiDF6D4FixedGridShard060EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard060EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard060EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard060EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard060EvenComparisonData)

theorem suzukiDF6D4FixedGridShard060EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard060EvenSolveData =
      suzukiDF6D4FixedGridShard060EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard060Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard060EvenSolveData =
    suzukiDF6D4FixedGridShard060EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard060EvenCross_eq_live :
    suzukiDF6D4FixedGridShard060EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 60) := by
  have h := suzukiDF6D4FixedGridShard060Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard060EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 60)) at h
  exact h

theorem suzukiDF6D4FixedGridShard060EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard060EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 60 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 60 k) := by
    rw [suzukiDF6D4FixedGridShard060EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 60 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060EvenDotSoundness i
          suzukiDF6D4FixedGridShard060EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 60 k) := by
    simpa [suzukiDF6D4FixedGridShard060EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard060EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 60 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 60) := by
    rw [suzukiDF6D4FixedGridShard060EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 60)
  rw [suzukiDF6D4FixedGridShard060EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard060EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard060EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard060EvenDotSoundness i
            suzukiDF6D4FixedGridShard060EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard060EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard060OddComparison_eq_live :
    suzukiDF6D4FixedGridShard060OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 60 k) := by
  have h := suzukiDF6D4FixedGridShard060Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard060OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 60 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard060OddCross_eq_live :
    suzukiDF6D4FixedGridShard060OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 60) := by
  have h := suzukiDF6D4FixedGridShard060Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard060OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 60)) at h
  exact h

def suzukiDF6D4FixedGridShard060OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard060OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard060OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard060OddDotSoundness i.val
      suzukiDF6D4FixedGridShard060OddComparisonData)

theorem suzukiDF6D4FixedGridShard060OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard060OddSolveData =
      suzukiDF6D4FixedGridShard060OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard060Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard060OddSolveData =
    suzukiDF6D4FixedGridShard060OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard060OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard060OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 60 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 60 k) := by
    rw [suzukiDF6D4FixedGridShard060OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 60 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060OddDotSoundness i
          suzukiDF6D4FixedGridShard060OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 60 k) := by
    simpa [suzukiDF6D4FixedGridShard060OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard060OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 60 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 60) := by
    rw [suzukiDF6D4FixedGridShard060OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 60)
  rw [suzukiDF6D4FixedGridShard060OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard060OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard060OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard060OddDotSoundness i
            suzukiDF6D4FixedGridShard060OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard060OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard060EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard060EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 361) := by
  have h := suzukiDF6D4FixedGridShard060Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard060EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 361)) at h
  exact h

theorem suzukiDF6D4FixedGridShard060EvenFull_eq_live :
    suzukiDF6D4FixedGridShard060EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 361) := by
  have h := suzukiDF6D4FixedGridShard060Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard060EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 361)) at h
  exact h

def suzukiDF6D4FixedGridShard060EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard060EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard060EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard060EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard060EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard060EvenResidualData =
      suzukiDF6D4FixedGridShard060EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard060Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard060EvenResidualData =
    suzukiDF6D4FixedGridShard060EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard060EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard060EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 361 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 361) := by
    rw [suzukiDF6D4FixedGridShard060EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 361
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060EvenDotSoundness i
          suzukiDF6D4FixedGridShard060EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 361) := by
    simpa [suzukiDF6D4FixedGridShard060EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard060EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 361) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 361) := by
    rw [suzukiDF6D4FixedGridShard060EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 361
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard060EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard060EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard060EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard060EvenDotSoundness i
            suzukiDF6D4FixedGridShard060EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard060EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard060OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard060OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 361) := by
  have h := suzukiDF6D4FixedGridShard060Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard060OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 361)) at h
  exact h

theorem suzukiDF6D4FixedGridShard060OddFull_eq_live :
    suzukiDF6D4FixedGridShard060OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 361) := by
  have h := suzukiDF6D4FixedGridShard060Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard060OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 361)) at h
  exact h

def suzukiDF6D4FixedGridShard060OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard060OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard060OddDotSoundness i.val
        suzukiDF6D4FixedGridShard060OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard060OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard060OddResidualData =
      suzukiDF6D4FixedGridShard060OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard060Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard060OddResidualData =
    suzukiDF6D4FixedGridShard060OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard060OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard060OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 361 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 361) := by
    rw [suzukiDF6D4FixedGridShard060OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 361
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060OddDotSoundness i
          suzukiDF6D4FixedGridShard060OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 361) := by
    simpa [suzukiDF6D4FixedGridShard060OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard060OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 361) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard060OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 361) := by
    rw [suzukiDF6D4FixedGridShard060OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 361
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard060OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard060OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard060OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard060OddDotSoundness i
            suzukiDF6D4FixedGridShard060OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard060OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
