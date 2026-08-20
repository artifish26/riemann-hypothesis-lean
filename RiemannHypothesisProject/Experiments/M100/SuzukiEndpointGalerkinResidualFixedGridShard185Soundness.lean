import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard185Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard185Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard185EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard185EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 185 k) := by
  have h := suzukiDF6D4FixedGridShard185Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard185EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 185 k)) at h
  exact h

def suzukiDF6D4FixedGridShard185EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard185EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard185EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard185EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard185EvenComparisonData)

theorem suzukiDF6D4FixedGridShard185EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard185EvenSolveData =
      suzukiDF6D4FixedGridShard185EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard185Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard185EvenSolveData =
    suzukiDF6D4FixedGridShard185EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard185EvenCross_eq_live :
    suzukiDF6D4FixedGridShard185EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 185) := by
  have h := suzukiDF6D4FixedGridShard185Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard185EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 185)) at h
  exact h

theorem suzukiDF6D4FixedGridShard185EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard185EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 185 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 185 k) := by
    rw [suzukiDF6D4FixedGridShard185EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 185 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185EvenDotSoundness i
          suzukiDF6D4FixedGridShard185EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 185 k) := by
    simpa [suzukiDF6D4FixedGridShard185EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard185EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 185 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 185) := by
    rw [suzukiDF6D4FixedGridShard185EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 185)
  rw [suzukiDF6D4FixedGridShard185EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard185EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard185EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard185EvenDotSoundness i
            suzukiDF6D4FixedGridShard185EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard185EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard185OddComparison_eq_live :
    suzukiDF6D4FixedGridShard185OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 185 k) := by
  have h := suzukiDF6D4FixedGridShard185Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard185OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 185 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard185OddCross_eq_live :
    suzukiDF6D4FixedGridShard185OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 185) := by
  have h := suzukiDF6D4FixedGridShard185Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard185OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 185)) at h
  exact h

def suzukiDF6D4FixedGridShard185OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard185OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard185OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard185OddDotSoundness i.val
      suzukiDF6D4FixedGridShard185OddComparisonData)

theorem suzukiDF6D4FixedGridShard185OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard185OddSolveData =
      suzukiDF6D4FixedGridShard185OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard185Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard185OddSolveData =
    suzukiDF6D4FixedGridShard185OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard185OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard185OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 185 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 185 k) := by
    rw [suzukiDF6D4FixedGridShard185OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 185 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185OddDotSoundness i
          suzukiDF6D4FixedGridShard185OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 185 k) := by
    simpa [suzukiDF6D4FixedGridShard185OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard185OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 185 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 185) := by
    rw [suzukiDF6D4FixedGridShard185OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 185)
  rw [suzukiDF6D4FixedGridShard185OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard185OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard185OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard185OddDotSoundness i
            suzukiDF6D4FixedGridShard185OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard185OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard185EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard185EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 486) := by
  have h := suzukiDF6D4FixedGridShard185Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard185EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 486)) at h
  exact h

theorem suzukiDF6D4FixedGridShard185EvenFull_eq_live :
    suzukiDF6D4FixedGridShard185EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 486) := by
  have h := suzukiDF6D4FixedGridShard185Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard185EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 486)) at h
  exact h

def suzukiDF6D4FixedGridShard185EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard185EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard185EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard185EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard185EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard185EvenResidualData =
      suzukiDF6D4FixedGridShard185EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard185Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard185EvenResidualData =
    suzukiDF6D4FixedGridShard185EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard185EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard185EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 486 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 486) := by
    rw [suzukiDF6D4FixedGridShard185EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 486
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185EvenDotSoundness i
          suzukiDF6D4FixedGridShard185EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 486) := by
    simpa [suzukiDF6D4FixedGridShard185EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard185EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 486) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 486) := by
    rw [suzukiDF6D4FixedGridShard185EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 486
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard185EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard185EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard185EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard185EvenDotSoundness i
            suzukiDF6D4FixedGridShard185EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard185EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard185OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard185OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 486) := by
  have h := suzukiDF6D4FixedGridShard185Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard185OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 486)) at h
  exact h

theorem suzukiDF6D4FixedGridShard185OddFull_eq_live :
    suzukiDF6D4FixedGridShard185OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 486) := by
  have h := suzukiDF6D4FixedGridShard185Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard185OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 486)) at h
  exact h

def suzukiDF6D4FixedGridShard185OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard185OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard185OddDotSoundness i.val
        suzukiDF6D4FixedGridShard185OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard185OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard185OddResidualData =
      suzukiDF6D4FixedGridShard185OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard185Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard185OddResidualData =
    suzukiDF6D4FixedGridShard185OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard185OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard185OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 486 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 486) := by
    rw [suzukiDF6D4FixedGridShard185OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 486
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185OddDotSoundness i
          suzukiDF6D4FixedGridShard185OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 486) := by
    simpa [suzukiDF6D4FixedGridShard185OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard185OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 486) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard185OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 486) := by
    rw [suzukiDF6D4FixedGridShard185OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 486
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard185OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard185OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard185OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard185OddDotSoundness i
            suzukiDF6D4FixedGridShard185OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard185OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
