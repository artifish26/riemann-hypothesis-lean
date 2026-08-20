import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard034Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard034Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard034EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard034EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 34 k) := by
  have h := suzukiDF6D4FixedGridShard034Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard034EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 34 k)) at h
  exact h

def suzukiDF6D4FixedGridShard034EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard034EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard034EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard034EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard034EvenComparisonData)

theorem suzukiDF6D4FixedGridShard034EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard034EvenSolveData =
      suzukiDF6D4FixedGridShard034EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard034Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard034EvenSolveData =
    suzukiDF6D4FixedGridShard034EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard034EvenCross_eq_live :
    suzukiDF6D4FixedGridShard034EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 34) := by
  have h := suzukiDF6D4FixedGridShard034Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard034EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 34)) at h
  exact h

theorem suzukiDF6D4FixedGridShard034EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard034EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 34 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 34 k) := by
    rw [suzukiDF6D4FixedGridShard034EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 34 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034EvenDotSoundness i
          suzukiDF6D4FixedGridShard034EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 34 k) := by
    simpa [suzukiDF6D4FixedGridShard034EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard034EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 34 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 34) := by
    rw [suzukiDF6D4FixedGridShard034EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 34)
  rw [suzukiDF6D4FixedGridShard034EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard034EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard034EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard034EvenDotSoundness i
            suzukiDF6D4FixedGridShard034EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard034EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard034OddComparison_eq_live :
    suzukiDF6D4FixedGridShard034OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 34 k) := by
  have h := suzukiDF6D4FixedGridShard034Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard034OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 34 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard034OddCross_eq_live :
    suzukiDF6D4FixedGridShard034OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 34) := by
  have h := suzukiDF6D4FixedGridShard034Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard034OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 34)) at h
  exact h

def suzukiDF6D4FixedGridShard034OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard034OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard034OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard034OddDotSoundness i.val
      suzukiDF6D4FixedGridShard034OddComparisonData)

theorem suzukiDF6D4FixedGridShard034OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard034OddSolveData =
      suzukiDF6D4FixedGridShard034OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard034Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard034OddSolveData =
    suzukiDF6D4FixedGridShard034OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard034OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard034OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 34 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 34 k) := by
    rw [suzukiDF6D4FixedGridShard034OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 34 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034OddDotSoundness i
          suzukiDF6D4FixedGridShard034OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 34 k) := by
    simpa [suzukiDF6D4FixedGridShard034OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard034OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 34 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 34) := by
    rw [suzukiDF6D4FixedGridShard034OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 34)
  rw [suzukiDF6D4FixedGridShard034OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard034OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard034OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard034OddDotSoundness i
            suzukiDF6D4FixedGridShard034OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard034OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard034EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard034EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 335) := by
  have h := suzukiDF6D4FixedGridShard034Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard034EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 335)) at h
  exact h

theorem suzukiDF6D4FixedGridShard034EvenFull_eq_live :
    suzukiDF6D4FixedGridShard034EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 335) := by
  have h := suzukiDF6D4FixedGridShard034Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard034EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 335)) at h
  exact h

def suzukiDF6D4FixedGridShard034EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard034EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard034EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard034EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard034EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard034EvenResidualData =
      suzukiDF6D4FixedGridShard034EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard034Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard034EvenResidualData =
    suzukiDF6D4FixedGridShard034EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard034EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard034EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 335 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 335) := by
    rw [suzukiDF6D4FixedGridShard034EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 335
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034EvenDotSoundness i
          suzukiDF6D4FixedGridShard034EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 335) := by
    simpa [suzukiDF6D4FixedGridShard034EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard034EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 335) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 335) := by
    rw [suzukiDF6D4FixedGridShard034EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 335
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard034EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard034EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard034EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard034EvenDotSoundness i
            suzukiDF6D4FixedGridShard034EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard034EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard034OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard034OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 335) := by
  have h := suzukiDF6D4FixedGridShard034Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard034OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 335)) at h
  exact h

theorem suzukiDF6D4FixedGridShard034OddFull_eq_live :
    suzukiDF6D4FixedGridShard034OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 335) := by
  have h := suzukiDF6D4FixedGridShard034Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard034OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 335)) at h
  exact h

def suzukiDF6D4FixedGridShard034OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard034OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard034OddDotSoundness i.val
        suzukiDF6D4FixedGridShard034OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard034OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard034OddResidualData =
      suzukiDF6D4FixedGridShard034OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard034Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard034OddResidualData =
    suzukiDF6D4FixedGridShard034OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard034OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard034OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 335 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 335) := by
    rw [suzukiDF6D4FixedGridShard034OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 335
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034OddDotSoundness i
          suzukiDF6D4FixedGridShard034OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 335) := by
    simpa [suzukiDF6D4FixedGridShard034OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard034OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 335) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard034OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 335) := by
    rw [suzukiDF6D4FixedGridShard034OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 335
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard034OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard034OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard034OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard034OddDotSoundness i
            suzukiDF6D4FixedGridShard034OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard034OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
