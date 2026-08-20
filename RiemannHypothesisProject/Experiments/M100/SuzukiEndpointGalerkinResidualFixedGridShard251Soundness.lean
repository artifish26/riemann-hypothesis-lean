import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard251Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard251Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard251EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard251EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 251 k) := by
  have h := suzukiDF6D4FixedGridShard251Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard251EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 251 k)) at h
  exact h

def suzukiDF6D4FixedGridShard251EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard251EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard251EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard251EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard251EvenComparisonData)

theorem suzukiDF6D4FixedGridShard251EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard251EvenSolveData =
      suzukiDF6D4FixedGridShard251EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard251Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard251EvenSolveData =
    suzukiDF6D4FixedGridShard251EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard251EvenCross_eq_live :
    suzukiDF6D4FixedGridShard251EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 251) := by
  have h := suzukiDF6D4FixedGridShard251Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard251EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 251)) at h
  exact h

theorem suzukiDF6D4FixedGridShard251EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard251EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 251 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 251 k) := by
    rw [suzukiDF6D4FixedGridShard251EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 251 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251EvenDotSoundness i
          suzukiDF6D4FixedGridShard251EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 251 k) := by
    simpa [suzukiDF6D4FixedGridShard251EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard251EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 251 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 251) := by
    rw [suzukiDF6D4FixedGridShard251EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 251)
  rw [suzukiDF6D4FixedGridShard251EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard251EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard251EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard251EvenDotSoundness i
            suzukiDF6D4FixedGridShard251EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard251EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard251OddComparison_eq_live :
    suzukiDF6D4FixedGridShard251OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 251 k) := by
  have h := suzukiDF6D4FixedGridShard251Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard251OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 251 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard251OddCross_eq_live :
    suzukiDF6D4FixedGridShard251OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 251) := by
  have h := suzukiDF6D4FixedGridShard251Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard251OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 251)) at h
  exact h

def suzukiDF6D4FixedGridShard251OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard251OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard251OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard251OddDotSoundness i.val
      suzukiDF6D4FixedGridShard251OddComparisonData)

theorem suzukiDF6D4FixedGridShard251OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard251OddSolveData =
      suzukiDF6D4FixedGridShard251OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard251Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard251OddSolveData =
    suzukiDF6D4FixedGridShard251OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard251OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard251OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 251 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 251 k) := by
    rw [suzukiDF6D4FixedGridShard251OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 251 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251OddDotSoundness i
          suzukiDF6D4FixedGridShard251OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 251 k) := by
    simpa [suzukiDF6D4FixedGridShard251OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard251OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 251 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 251) := by
    rw [suzukiDF6D4FixedGridShard251OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 251)
  rw [suzukiDF6D4FixedGridShard251OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard251OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard251OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard251OddDotSoundness i
            suzukiDF6D4FixedGridShard251OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard251OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard251EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard251EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 552) := by
  have h := suzukiDF6D4FixedGridShard251Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard251EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 552)) at h
  exact h

theorem suzukiDF6D4FixedGridShard251EvenFull_eq_live :
    suzukiDF6D4FixedGridShard251EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 552) := by
  have h := suzukiDF6D4FixedGridShard251Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard251EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 552)) at h
  exact h

def suzukiDF6D4FixedGridShard251EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard251EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard251EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard251EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard251EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard251EvenResidualData =
      suzukiDF6D4FixedGridShard251EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard251Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard251EvenResidualData =
    suzukiDF6D4FixedGridShard251EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard251EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard251EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 552 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 552) := by
    rw [suzukiDF6D4FixedGridShard251EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 552
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251EvenDotSoundness i
          suzukiDF6D4FixedGridShard251EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 552) := by
    simpa [suzukiDF6D4FixedGridShard251EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard251EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 552) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 552) := by
    rw [suzukiDF6D4FixedGridShard251EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 552
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard251EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard251EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard251EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard251EvenDotSoundness i
            suzukiDF6D4FixedGridShard251EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard251EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard251OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard251OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 552) := by
  have h := suzukiDF6D4FixedGridShard251Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard251OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 552)) at h
  exact h

theorem suzukiDF6D4FixedGridShard251OddFull_eq_live :
    suzukiDF6D4FixedGridShard251OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 552) := by
  have h := suzukiDF6D4FixedGridShard251Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard251OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 552)) at h
  exact h

def suzukiDF6D4FixedGridShard251OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard251OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard251OddDotSoundness i.val
        suzukiDF6D4FixedGridShard251OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard251OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard251OddResidualData =
      suzukiDF6D4FixedGridShard251OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard251Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard251OddResidualData =
    suzukiDF6D4FixedGridShard251OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard251OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard251OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 552 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 552) := by
    rw [suzukiDF6D4FixedGridShard251OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 552
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251OddDotSoundness i
          suzukiDF6D4FixedGridShard251OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 552) := by
    simpa [suzukiDF6D4FixedGridShard251OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard251OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 552) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard251OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 552) := by
    rw [suzukiDF6D4FixedGridShard251OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 552
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard251OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard251OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard251OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard251OddDotSoundness i
            suzukiDF6D4FixedGridShard251OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard251OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
