import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard197Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard197Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard197EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard197EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 197 k) := by
  have h := suzukiDF6D4FixedGridShard197Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard197EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 197 k)) at h
  exact h

def suzukiDF6D4FixedGridShard197EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard197EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard197EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard197EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard197EvenComparisonData)

theorem suzukiDF6D4FixedGridShard197EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard197EvenSolveData =
      suzukiDF6D4FixedGridShard197EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard197Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard197EvenSolveData =
    suzukiDF6D4FixedGridShard197EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard197EvenCross_eq_live :
    suzukiDF6D4FixedGridShard197EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 197) := by
  have h := suzukiDF6D4FixedGridShard197Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard197EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 197)) at h
  exact h

theorem suzukiDF6D4FixedGridShard197EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard197EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 197 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 197 k) := by
    rw [suzukiDF6D4FixedGridShard197EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 197 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197EvenDotSoundness i
          suzukiDF6D4FixedGridShard197EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 197 k) := by
    simpa [suzukiDF6D4FixedGridShard197EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard197EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 197 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 197) := by
    rw [suzukiDF6D4FixedGridShard197EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 197)
  rw [suzukiDF6D4FixedGridShard197EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard197EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard197EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard197EvenDotSoundness i
            suzukiDF6D4FixedGridShard197EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard197EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard197OddComparison_eq_live :
    suzukiDF6D4FixedGridShard197OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 197 k) := by
  have h := suzukiDF6D4FixedGridShard197Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard197OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 197 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard197OddCross_eq_live :
    suzukiDF6D4FixedGridShard197OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 197) := by
  have h := suzukiDF6D4FixedGridShard197Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard197OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 197)) at h
  exact h

def suzukiDF6D4FixedGridShard197OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard197OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard197OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard197OddDotSoundness i.val
      suzukiDF6D4FixedGridShard197OddComparisonData)

theorem suzukiDF6D4FixedGridShard197OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard197OddSolveData =
      suzukiDF6D4FixedGridShard197OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard197Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard197OddSolveData =
    suzukiDF6D4FixedGridShard197OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard197OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard197OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 197 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 197 k) := by
    rw [suzukiDF6D4FixedGridShard197OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 197 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197OddDotSoundness i
          suzukiDF6D4FixedGridShard197OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 197 k) := by
    simpa [suzukiDF6D4FixedGridShard197OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard197OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 197 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 197) := by
    rw [suzukiDF6D4FixedGridShard197OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 197)
  rw [suzukiDF6D4FixedGridShard197OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard197OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard197OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard197OddDotSoundness i
            suzukiDF6D4FixedGridShard197OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard197OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard197EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard197EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 498) := by
  have h := suzukiDF6D4FixedGridShard197Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard197EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 498)) at h
  exact h

theorem suzukiDF6D4FixedGridShard197EvenFull_eq_live :
    suzukiDF6D4FixedGridShard197EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 498) := by
  have h := suzukiDF6D4FixedGridShard197Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard197EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 498)) at h
  exact h

def suzukiDF6D4FixedGridShard197EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard197EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard197EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard197EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard197EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard197EvenResidualData =
      suzukiDF6D4FixedGridShard197EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard197Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard197EvenResidualData =
    suzukiDF6D4FixedGridShard197EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard197EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard197EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 498 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 498) := by
    rw [suzukiDF6D4FixedGridShard197EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 498
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197EvenDotSoundness i
          suzukiDF6D4FixedGridShard197EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 498) := by
    simpa [suzukiDF6D4FixedGridShard197EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard197EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 498) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 498) := by
    rw [suzukiDF6D4FixedGridShard197EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 498
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard197EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard197EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard197EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard197EvenDotSoundness i
            suzukiDF6D4FixedGridShard197EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard197EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard197OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard197OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 498) := by
  have h := suzukiDF6D4FixedGridShard197Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard197OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 498)) at h
  exact h

theorem suzukiDF6D4FixedGridShard197OddFull_eq_live :
    suzukiDF6D4FixedGridShard197OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 498) := by
  have h := suzukiDF6D4FixedGridShard197Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard197OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 498)) at h
  exact h

def suzukiDF6D4FixedGridShard197OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard197OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard197OddDotSoundness i.val
        suzukiDF6D4FixedGridShard197OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard197OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard197OddResidualData =
      suzukiDF6D4FixedGridShard197OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard197Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard197OddResidualData =
    suzukiDF6D4FixedGridShard197OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard197OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard197OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 498 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 498) := by
    rw [suzukiDF6D4FixedGridShard197OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 498
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197OddDotSoundness i
          suzukiDF6D4FixedGridShard197OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 498) := by
    simpa [suzukiDF6D4FixedGridShard197OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard197OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 498) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard197OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 498) := by
    rw [suzukiDF6D4FixedGridShard197OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 498
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard197OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard197OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard197OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard197OddDotSoundness i
            suzukiDF6D4FixedGridShard197OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard197OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
