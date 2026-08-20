import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard162Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard162Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard162EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard162EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 162 k) := by
  have h := suzukiDF6D4FixedGridShard162Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard162EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 162 k)) at h
  exact h

def suzukiDF6D4FixedGridShard162EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard162EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard162EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard162EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard162EvenComparisonData)

theorem suzukiDF6D4FixedGridShard162EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard162EvenSolveData =
      suzukiDF6D4FixedGridShard162EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard162Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard162EvenSolveData =
    suzukiDF6D4FixedGridShard162EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard162EvenCross_eq_live :
    suzukiDF6D4FixedGridShard162EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 162) := by
  have h := suzukiDF6D4FixedGridShard162Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard162EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 162)) at h
  exact h

theorem suzukiDF6D4FixedGridShard162EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard162EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 162 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 162 k) := by
    rw [suzukiDF6D4FixedGridShard162EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 162 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162EvenDotSoundness i
          suzukiDF6D4FixedGridShard162EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 162 k) := by
    simpa [suzukiDF6D4FixedGridShard162EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard162EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 162 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 162) := by
    rw [suzukiDF6D4FixedGridShard162EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 162)
  rw [suzukiDF6D4FixedGridShard162EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard162EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard162EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard162EvenDotSoundness i
            suzukiDF6D4FixedGridShard162EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard162EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard162OddComparison_eq_live :
    suzukiDF6D4FixedGridShard162OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 162 k) := by
  have h := suzukiDF6D4FixedGridShard162Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard162OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 162 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard162OddCross_eq_live :
    suzukiDF6D4FixedGridShard162OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 162) := by
  have h := suzukiDF6D4FixedGridShard162Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard162OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 162)) at h
  exact h

def suzukiDF6D4FixedGridShard162OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard162OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard162OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard162OddDotSoundness i.val
      suzukiDF6D4FixedGridShard162OddComparisonData)

theorem suzukiDF6D4FixedGridShard162OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard162OddSolveData =
      suzukiDF6D4FixedGridShard162OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard162Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard162OddSolveData =
    suzukiDF6D4FixedGridShard162OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard162OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard162OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 162 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 162 k) := by
    rw [suzukiDF6D4FixedGridShard162OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 162 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162OddDotSoundness i
          suzukiDF6D4FixedGridShard162OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 162 k) := by
    simpa [suzukiDF6D4FixedGridShard162OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard162OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 162 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 162) := by
    rw [suzukiDF6D4FixedGridShard162OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 162)
  rw [suzukiDF6D4FixedGridShard162OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard162OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard162OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard162OddDotSoundness i
            suzukiDF6D4FixedGridShard162OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard162OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard162EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard162EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 463) := by
  have h := suzukiDF6D4FixedGridShard162Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard162EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 463)) at h
  exact h

theorem suzukiDF6D4FixedGridShard162EvenFull_eq_live :
    suzukiDF6D4FixedGridShard162EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 463) := by
  have h := suzukiDF6D4FixedGridShard162Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard162EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 463)) at h
  exact h

def suzukiDF6D4FixedGridShard162EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard162EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard162EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard162EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard162EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard162EvenResidualData =
      suzukiDF6D4FixedGridShard162EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard162Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard162EvenResidualData =
    suzukiDF6D4FixedGridShard162EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard162EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard162EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 463 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 463) := by
    rw [suzukiDF6D4FixedGridShard162EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 463
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162EvenDotSoundness i
          suzukiDF6D4FixedGridShard162EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 463) := by
    simpa [suzukiDF6D4FixedGridShard162EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard162EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 463) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 463) := by
    rw [suzukiDF6D4FixedGridShard162EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 463
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard162EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard162EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard162EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard162EvenDotSoundness i
            suzukiDF6D4FixedGridShard162EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard162EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard162OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard162OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 463) := by
  have h := suzukiDF6D4FixedGridShard162Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard162OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 463)) at h
  exact h

theorem suzukiDF6D4FixedGridShard162OddFull_eq_live :
    suzukiDF6D4FixedGridShard162OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 463) := by
  have h := suzukiDF6D4FixedGridShard162Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard162OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 463)) at h
  exact h

def suzukiDF6D4FixedGridShard162OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard162OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard162OddDotSoundness i.val
        suzukiDF6D4FixedGridShard162OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard162OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard162OddResidualData =
      suzukiDF6D4FixedGridShard162OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard162Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard162OddResidualData =
    suzukiDF6D4FixedGridShard162OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard162OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard162OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 463 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 463) := by
    rw [suzukiDF6D4FixedGridShard162OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 463
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162OddDotSoundness i
          suzukiDF6D4FixedGridShard162OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 463) := by
    simpa [suzukiDF6D4FixedGridShard162OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard162OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 463) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard162OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 463) := by
    rw [suzukiDF6D4FixedGridShard162OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 463
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard162OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard162OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard162OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard162OddDotSoundness i
            suzukiDF6D4FixedGridShard162OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard162OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
