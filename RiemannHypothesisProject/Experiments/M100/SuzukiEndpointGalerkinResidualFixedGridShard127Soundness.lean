import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard127Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard127Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard127EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard127EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 127 k) := by
  have h := suzukiDF6D4FixedGridShard127Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard127EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 127 k)) at h
  exact h

def suzukiDF6D4FixedGridShard127EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard127EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard127EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard127EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard127EvenComparisonData)

theorem suzukiDF6D4FixedGridShard127EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard127EvenSolveData =
      suzukiDF6D4FixedGridShard127EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard127Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard127EvenSolveData =
    suzukiDF6D4FixedGridShard127EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard127EvenCross_eq_live :
    suzukiDF6D4FixedGridShard127EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 127) := by
  have h := suzukiDF6D4FixedGridShard127Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard127EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 127)) at h
  exact h

theorem suzukiDF6D4FixedGridShard127EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard127EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 127 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 127 k) := by
    rw [suzukiDF6D4FixedGridShard127EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 127 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127EvenDotSoundness i
          suzukiDF6D4FixedGridShard127EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 127 k) := by
    simpa [suzukiDF6D4FixedGridShard127EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard127EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 127 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 127) := by
    rw [suzukiDF6D4FixedGridShard127EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 127)
  rw [suzukiDF6D4FixedGridShard127EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard127EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard127EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard127EvenDotSoundness i
            suzukiDF6D4FixedGridShard127EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard127EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard127OddComparison_eq_live :
    suzukiDF6D4FixedGridShard127OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 127 k) := by
  have h := suzukiDF6D4FixedGridShard127Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard127OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 127 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard127OddCross_eq_live :
    suzukiDF6D4FixedGridShard127OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 127) := by
  have h := suzukiDF6D4FixedGridShard127Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard127OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 127)) at h
  exact h

def suzukiDF6D4FixedGridShard127OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard127OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard127OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard127OddDotSoundness i.val
      suzukiDF6D4FixedGridShard127OddComparisonData)

theorem suzukiDF6D4FixedGridShard127OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard127OddSolveData =
      suzukiDF6D4FixedGridShard127OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard127Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard127OddSolveData =
    suzukiDF6D4FixedGridShard127OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard127OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard127OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 127 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 127 k) := by
    rw [suzukiDF6D4FixedGridShard127OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 127 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127OddDotSoundness i
          suzukiDF6D4FixedGridShard127OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 127 k) := by
    simpa [suzukiDF6D4FixedGridShard127OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard127OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 127 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 127) := by
    rw [suzukiDF6D4FixedGridShard127OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 127)
  rw [suzukiDF6D4FixedGridShard127OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard127OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard127OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard127OddDotSoundness i
            suzukiDF6D4FixedGridShard127OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard127OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard127EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard127EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 428) := by
  have h := suzukiDF6D4FixedGridShard127Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard127EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 428)) at h
  exact h

theorem suzukiDF6D4FixedGridShard127EvenFull_eq_live :
    suzukiDF6D4FixedGridShard127EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 428) := by
  have h := suzukiDF6D4FixedGridShard127Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard127EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 428)) at h
  exact h

def suzukiDF6D4FixedGridShard127EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard127EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard127EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard127EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard127EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard127EvenResidualData =
      suzukiDF6D4FixedGridShard127EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard127Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard127EvenResidualData =
    suzukiDF6D4FixedGridShard127EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard127EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard127EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 428 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 428) := by
    rw [suzukiDF6D4FixedGridShard127EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 428
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127EvenDotSoundness i
          suzukiDF6D4FixedGridShard127EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 428) := by
    simpa [suzukiDF6D4FixedGridShard127EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard127EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 428) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 428) := by
    rw [suzukiDF6D4FixedGridShard127EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 428
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard127EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard127EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard127EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard127EvenDotSoundness i
            suzukiDF6D4FixedGridShard127EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard127EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard127OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard127OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 428) := by
  have h := suzukiDF6D4FixedGridShard127Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard127OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 428)) at h
  exact h

theorem suzukiDF6D4FixedGridShard127OddFull_eq_live :
    suzukiDF6D4FixedGridShard127OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 428) := by
  have h := suzukiDF6D4FixedGridShard127Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard127OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 428)) at h
  exact h

def suzukiDF6D4FixedGridShard127OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard127OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard127OddDotSoundness i.val
        suzukiDF6D4FixedGridShard127OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard127OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard127OddResidualData =
      suzukiDF6D4FixedGridShard127OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard127Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard127OddResidualData =
    suzukiDF6D4FixedGridShard127OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard127OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard127OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 428 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 428) := by
    rw [suzukiDF6D4FixedGridShard127OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 428
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127OddDotSoundness i
          suzukiDF6D4FixedGridShard127OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 428) := by
    simpa [suzukiDF6D4FixedGridShard127OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard127OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 428) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard127OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 428) := by
    rw [suzukiDF6D4FixedGridShard127OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 428
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard127OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard127OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard127OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard127OddDotSoundness i
            suzukiDF6D4FixedGridShard127OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard127OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
