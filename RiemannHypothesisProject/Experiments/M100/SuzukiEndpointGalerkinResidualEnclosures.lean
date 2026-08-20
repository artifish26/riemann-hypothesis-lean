import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointFullConvolutionEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointComparisonTable

/-!
# Frozen Galerkin residual enclosures for M100-DF6D4

This module evaluates the exact residual of the generated rational Galerkin
approximants.  The approximants are not asserted to solve an analytic system:
their nonzero residual on modes `45,...,300` is retained explicitly, as is the
residual prefix on modes `301,...,600`.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators
open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def suzukiDF6D4GalerkinMode (i : Fin 256) : Nat := 45 + i.val

def suzukiDF6D4EvenLowMode (i : Fin 45) : Nat := i.val

def suzukiDF6D4OddLowMode (i : Fin 44) : Nat := i.val + 1

def suzukiDF6D4EvenComparisonGalerkinEntry
    (i j : Fin 256) : Real :=
  if i = j then
    suzukiDF6D4EvenComparisonDiagonal (suzukiDF6D4GalerkinMode i)
  else if i.val < j.val then
    suzukiDF6D4ComparisonEvenOffDiagonal
      (suzukiDF6D4GalerkinMode i) (suzukiDF6D4GalerkinMode j)
  else
    suzukiDF6D4ComparisonEvenOffDiagonal
      (suzukiDF6D4GalerkinMode j) (suzukiDF6D4GalerkinMode i)

def suzukiDF6D4EvenComparisonGalerkinEntryInterval
    (i j : Fin 256) : RationalInterval :=
  if i = j then
    suzukiDF6D4TabulatedEvenComparisonDiagonalInterval
      (suzukiDF6D4GalerkinMode i)
  else if i.val < j.val then
    suzukiDF6D4ComparisonEvenOffDiagonalInterval
      (suzukiDF6D4GalerkinMode i) (suzukiDF6D4GalerkinMode j)
  else
    suzukiDF6D4ComparisonEvenOffDiagonalInterval
      (suzukiDF6D4GalerkinMode j) (suzukiDF6D4GalerkinMode i)

theorem suzukiDF6D4EvenComparisonGalerkinEntryInterval_contains
    (i j : Fin 256) :
    (suzukiDF6D4EvenComparisonGalerkinEntryInterval i j).Contains
      (suzukiDF6D4EvenComparisonGalerkinEntry i j) := by
  by_cases heq : i = j
  · subst j
    simp only [suzukiDF6D4EvenComparisonGalerkinEntryInterval,
      suzukiDF6D4EvenComparisonGalerkinEntry, if_pos]
    exact suzukiDF6D4TabulatedEvenComparisonDiagonalInterval_contains
      (suzukiDF6D4GalerkinMode i) (by simp [suzukiDF6D4GalerkinMode])
      (by have := i.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
  · by_cases hlt : i.val < j.val
    · simp only [suzukiDF6D4EvenComparisonGalerkinEntryInterval,
        suzukiDF6D4EvenComparisonGalerkinEntry, heq, hlt, if_false, if_true]
      exact suzukiDF6D4ComparisonEvenOffDiagonalInterval_contains _ _
        (by simp [suzukiDF6D4GalerkinMode])
        (by simp [suzukiDF6D4GalerkinMode]; omega)
    · have hji : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
        omega
      simp only [suzukiDF6D4EvenComparisonGalerkinEntryInterval,
        suzukiDF6D4EvenComparisonGalerkinEntry, heq, hlt, if_false]
      exact suzukiDF6D4ComparisonEvenOffDiagonalInterval_contains _ _
        (by simp [suzukiDF6D4GalerkinMode])
        (by simp [suzukiDF6D4GalerkinMode]; omega)

def suzukiDF6D4OddComparisonGalerkinEntry
    (i j : Fin 256) : Real :=
  if i = j then
    suzukiDF6D4OddComparisonDiagonal (suzukiDF6D4GalerkinMode i)
  else if i.val < j.val then
    suzukiDF6D4ComparisonOddOffDiagonal
      (suzukiDF6D4GalerkinMode i) (suzukiDF6D4GalerkinMode j)
  else
    suzukiDF6D4ComparisonOddOffDiagonal
      (suzukiDF6D4GalerkinMode j) (suzukiDF6D4GalerkinMode i)

def suzukiDF6D4OddComparisonGalerkinEntryInterval
    (i j : Fin 256) : RationalInterval :=
  if i = j then
    suzukiDF6D4TabulatedOddComparisonDiagonalInterval
      (suzukiDF6D4GalerkinMode i)
  else if i.val < j.val then
    suzukiDF6D4ComparisonOddOffDiagonalInterval
      (suzukiDF6D4GalerkinMode i) (suzukiDF6D4GalerkinMode j)
  else
    suzukiDF6D4ComparisonOddOffDiagonalInterval
      (suzukiDF6D4GalerkinMode j) (suzukiDF6D4GalerkinMode i)

theorem suzukiDF6D4OddComparisonGalerkinEntryInterval_contains
    (i j : Fin 256) :
    (suzukiDF6D4OddComparisonGalerkinEntryInterval i j).Contains
      (suzukiDF6D4OddComparisonGalerkinEntry i j) := by
  by_cases heq : i = j
  · subst j
    simp only [suzukiDF6D4OddComparisonGalerkinEntryInterval,
      suzukiDF6D4OddComparisonGalerkinEntry, if_pos]
    exact suzukiDF6D4TabulatedOddComparisonDiagonalInterval_contains
      (suzukiDF6D4GalerkinMode i) (by simp [suzukiDF6D4GalerkinMode])
      (by have := i.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
  · by_cases hlt : i.val < j.val
    · simp only [suzukiDF6D4OddComparisonGalerkinEntryInterval,
        suzukiDF6D4OddComparisonGalerkinEntry, heq, hlt, if_false, if_true]
      exact suzukiDF6D4ComparisonOddOffDiagonalInterval_contains _ _
        (by simp [suzukiDF6D4GalerkinMode])
        (by simp [suzukiDF6D4GalerkinMode]; omega)
    · have hji : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
        omega
      simp only [suzukiDF6D4OddComparisonGalerkinEntryInterval,
        suzukiDF6D4OddComparisonGalerkinEntry, heq, hlt, if_false]
      exact suzukiDF6D4ComparisonOddOffDiagonalInterval_contains _ _
        (by simp [suzukiDF6D4GalerkinMode])
        (by simp [suzukiDF6D4GalerkinMode]; omega)

def suzukiDF6D4EvenCompleteCrossEntry (i : Fin 45) (j : Fin 256) : Real :=
  suzukiDF6D4EvenOffDiagonal
    (suzukiDF6D4EvenLowMode i) (suzukiDF6D4GalerkinMode j)

def suzukiDF6D4EvenCompleteCrossEntryInterval
    (i : Fin 45) (j : Fin 256) : RationalInterval :=
  suzukiDF6D4FullEvenOffDiagonalInterval
    (suzukiDF6D4EvenLowMode i) (suzukiDF6D4GalerkinMode j)

theorem suzukiDF6D4EvenCompleteCrossEntryInterval_contains
    (i : Fin 45) (j : Fin 256) :
    (suzukiDF6D4EvenCompleteCrossEntryInterval i j).Contains
      (suzukiDF6D4EvenCompleteCrossEntry i j) := by
  exact suzukiDF6D4FullEvenOffDiagonalInterval_contains _ _
    (by simp [suzukiDF6D4EvenLowMode, suzukiDF6D4GalerkinMode]; omega)
    (by have := j.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)

def suzukiDF6D4OddCompleteCrossEntry (i : Fin 44) (j : Fin 256) : Real :=
  suzukiDF6D4OddOffDiagonal
    (suzukiDF6D4OddLowMode i) (suzukiDF6D4GalerkinMode j)

def suzukiDF6D4OddCompleteCrossEntryInterval
    (i : Fin 44) (j : Fin 256) : RationalInterval :=
  suzukiDF6D4FullOddOffDiagonalInterval
    (suzukiDF6D4OddLowMode i) (suzukiDF6D4GalerkinMode j)

theorem suzukiDF6D4OddCompleteCrossEntryInterval_contains
    (i : Fin 44) (j : Fin 256) :
    (suzukiDF6D4OddCompleteCrossEntryInterval i j).Contains
      (suzukiDF6D4OddCompleteCrossEntry i j) := by
  exact suzukiDF6D4FullOddOffDiagonalInterval_contains _ _
    (by simp [suzukiDF6D4OddLowMode])
    (by simp [suzukiDF6D4OddLowMode, suzukiDF6D4GalerkinMode]; omega)
    (by have := j.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)

def suzukiDF6D4EvenGalerkinSolveResidual
    (j : Fin 256) (i : Fin 45) : Real :=
  suzukiDF6D4EvenCompleteCrossEntry i j -
    ∑ k : Fin 256,
      suzukiDF6D4EvenComparisonGalerkinEntry j k *
        (suzukiDF6D4EvenGalerkinApproximant k i : Real)

def suzukiDF6D4EvenGalerkinSolveResidualInterval
    (j : Fin 256) (i : Fin 45) : RationalInterval :=
  (suzukiDF6D4EvenCompleteCrossEntryInterval i j).sub
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k i)
        (suzukiDF6D4EvenComparisonGalerkinEntryInterval j k))

theorem suzukiDF6D4EvenGalerkinSolveResidualInterval_contains
    (j : Fin 256) (i : Fin 45) :
    (suzukiDF6D4EvenGalerkinSolveResidualInterval j i).Contains
      (suzukiDF6D4EvenGalerkinSolveResidual j i) := by
  exact RationalInterval.contains_sub
    (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i j)
    (RationalInterval.contains_sum fun k _ =>
      (by
        simpa only [mul_comm] using RationalInterval.contains_scale
          (suzukiDF6D4EvenGalerkinApproximant k i)
          (suzukiDF6D4EvenComparisonGalerkinEntryInterval_contains j k)))

def suzukiDF6D4OddGalerkinSolveResidual
    (j : Fin 256) (i : Fin 44) : Real :=
  suzukiDF6D4OddCompleteCrossEntry i j -
    ∑ k : Fin 256,
      suzukiDF6D4OddComparisonGalerkinEntry j k *
        (suzukiDF6D4OddGalerkinApproximant k i : Real)

def suzukiDF6D4OddGalerkinSolveResidualInterval
    (j : Fin 256) (i : Fin 44) : RationalInterval :=
  (suzukiDF6D4OddCompleteCrossEntryInterval i j).sub
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k i)
        (suzukiDF6D4OddComparisonGalerkinEntryInterval j k))

theorem suzukiDF6D4OddGalerkinSolveResidualInterval_contains
    (j : Fin 256) (i : Fin 44) :
    (suzukiDF6D4OddGalerkinSolveResidualInterval j i).Contains
      (suzukiDF6D4OddGalerkinSolveResidual j i) := by
  exact RationalInterval.contains_sub
    (suzukiDF6D4OddCompleteCrossEntryInterval_contains i j)
    (RationalInterval.contains_sum fun k _ =>
      (by
        simpa only [mul_comm] using RationalInterval.contains_scale
          (suzukiDF6D4OddGalerkinApproximant k i)
          (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains j k)))

def suzukiDF6D4EvenResidualColumn
    (mode : Nat) (i : Fin 45) : Real :=
  suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) mode -
    ∑ k : Fin 256,
      (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
        suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) mode

def suzukiDF6D4EvenResidualColumnInterval
    (mode : Nat) (i : Fin 45) : RationalInterval :=
  (suzukiDF6D4FullEvenOffDiagonalInterval
      (suzukiDF6D4EvenLowMode i) mode).sub
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k i)
        (suzukiDF6D4ComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) mode))

theorem suzukiDF6D4EvenResidualColumnInterval_contains
    (mode : Nat) (hlower : 301 ≤ mode) (hupper : mode ≤ 602)
    (i : Fin 45) :
    (suzukiDF6D4EvenResidualColumnInterval mode i).Contains
      (suzukiDF6D4EvenResidualColumn mode i) := by
  exact RationalInterval.contains_sub
    (suzukiDF6D4FullEvenOffDiagonalInterval_contains _ _
      (by simp [suzukiDF6D4EvenLowMode]; omega) hupper)
    (RationalInterval.contains_sum fun k _ =>
      RationalInterval.contains_scale _
        (suzukiDF6D4ComparisonEvenOffDiagonalInterval_contains _ _
          (by simp [suzukiDF6D4GalerkinMode])
          (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)))

def suzukiDF6D4OddResidualColumn
    (mode : Nat) (i : Fin 44) : Real :=
  suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) mode -
    ∑ k : Fin 256,
      (suzukiDF6D4OddGalerkinApproximant k i : Real) *
        suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) mode

def suzukiDF6D4OddResidualColumnInterval
    (mode : Nat) (i : Fin 44) : RationalInterval :=
  (suzukiDF6D4FullOddOffDiagonalInterval
      (suzukiDF6D4OddLowMode i) mode).sub
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k i)
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) mode))

theorem suzukiDF6D4OddResidualColumnInterval_contains
    (mode : Nat) (hlower : 301 ≤ mode) (hupper : mode ≤ 602)
    (i : Fin 44) :
    (suzukiDF6D4OddResidualColumnInterval mode i).Contains
      (suzukiDF6D4OddResidualColumn mode i) := by
  exact RationalInterval.contains_sub
    (suzukiDF6D4FullOddOffDiagonalInterval_contains _ _
      (by simp [suzukiDF6D4OddLowMode])
      (by simp [suzukiDF6D4OddLowMode]; omega) hupper)
    (RationalInterval.contains_sum fun k _ =>
      RationalInterval.contains_scale _
        (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains _ _
          (by simp [suzukiDF6D4GalerkinMode])
          (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)))

def suzukiDF6D4EvenGalerkinBaseEntry (i j : Fin 45) : Real :=
  ∑ k : Fin 256,
    (suzukiDF6D4EvenCompleteCrossEntry i k *
        (suzukiDF6D4EvenGalerkinApproximant k j : Real) +
      (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
        suzukiDF6D4EvenGalerkinSolveResidual k j)

def suzukiDF6D4EvenGalerkinBaseEntryInterval
    (i j : Fin 45) : RationalInterval :=
  RationalInterval.sum Finset.univ fun k : Fin 256 =>
    (RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k j)
      (suzukiDF6D4EvenCompleteCrossEntryInterval i k)).add
    (RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k i)
      (suzukiDF6D4EvenGalerkinSolveResidualInterval k j))

theorem suzukiDF6D4EvenGalerkinBaseEntryInterval_contains (i j : Fin 45) :
    (suzukiDF6D4EvenGalerkinBaseEntryInterval i j).Contains
      (suzukiDF6D4EvenGalerkinBaseEntry i j) := by
  unfold suzukiDF6D4EvenGalerkinBaseEntryInterval
    suzukiDF6D4EvenGalerkinBaseEntry
  exact RationalInterval.contains_sum
    (s := Finset.univ)
    (f := fun k : Fin 256 =>
      (RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k j)
        (suzukiDF6D4EvenCompleteCrossEntryInterval i k)).add
      (RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k i)
        (suzukiDF6D4EvenGalerkinSolveResidualInterval k j)))
    (x := fun k : Fin 256 =>
      suzukiDF6D4EvenCompleteCrossEntry i k *
          (suzukiDF6D4EvenGalerkinApproximant k j : Real) +
        (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
          suzukiDF6D4EvenGalerkinSolveResidual k j)
    (fun k _ => RationalInterval.contains_add
      (by
        simpa only [mul_comm] using RationalInterval.contains_scale
          (suzukiDF6D4EvenGalerkinApproximant k j)
          (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i k))
      (RationalInterval.contains_scale (suzukiDF6D4EvenGalerkinApproximant k i)
        (suzukiDF6D4EvenGalerkinSolveResidualInterval_contains k j)))

def suzukiDF6D4OddGalerkinBaseEntry (i j : Fin 44) : Real :=
  ∑ k : Fin 256,
    (suzukiDF6D4OddCompleteCrossEntry i k *
        (suzukiDF6D4OddGalerkinApproximant k j : Real) +
      (suzukiDF6D4OddGalerkinApproximant k i : Real) *
        suzukiDF6D4OddGalerkinSolveResidual k j)

def suzukiDF6D4OddGalerkinBaseEntryInterval
    (i j : Fin 44) : RationalInterval :=
  RationalInterval.sum Finset.univ fun k : Fin 256 =>
    (RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k j)
      (suzukiDF6D4OddCompleteCrossEntryInterval i k)).add
    (RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k i)
      (suzukiDF6D4OddGalerkinSolveResidualInterval k j))

theorem suzukiDF6D4OddGalerkinBaseEntryInterval_contains (i j : Fin 44) :
    (suzukiDF6D4OddGalerkinBaseEntryInterval i j).Contains
      (suzukiDF6D4OddGalerkinBaseEntry i j) := by
  unfold suzukiDF6D4OddGalerkinBaseEntryInterval
    suzukiDF6D4OddGalerkinBaseEntry
  exact RationalInterval.contains_sum
    (s := Finset.univ)
    (f := fun k : Fin 256 =>
      (RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k j)
        (suzukiDF6D4OddCompleteCrossEntryInterval i k)).add
      (RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k i)
        (suzukiDF6D4OddGalerkinSolveResidualInterval k j)))
    (x := fun k : Fin 256 =>
      suzukiDF6D4OddCompleteCrossEntry i k *
          (suzukiDF6D4OddGalerkinApproximant k j : Real) +
        (suzukiDF6D4OddGalerkinApproximant k i : Real) *
          suzukiDF6D4OddGalerkinSolveResidual k j)
    (fun k _ => RationalInterval.contains_add
      (by
        simpa only [mul_comm] using RationalInterval.contains_scale
          (suzukiDF6D4OddGalerkinApproximant k j)
          (suzukiDF6D4OddCompleteCrossEntryInterval_contains i k))
      (RationalInterval.contains_scale (suzukiDF6D4OddGalerkinApproximant k i)
        (suzukiDF6D4OddGalerkinSolveResidualInterval_contains k j)))

def suzukiDF6D4EvenFiniteResidualGramEntry (i j : Fin 45) : Real :=
  (∑ k : Fin 256,
      suzukiDF6D4EvenGalerkinSolveResidual k i *
        suzukiDF6D4EvenGalerkinSolveResidual k j) +
    ∑ r : Fin 300,
      suzukiDF6D4EvenResidualColumn (301 + r.val) i *
        suzukiDF6D4EvenResidualColumn (301 + r.val) j

def suzukiDF6D4EvenFiniteResidualGramEntryInterval
    (i j : Fin 45) : RationalInterval :=
  (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      (suzukiDF6D4EvenGalerkinSolveResidualInterval k i).mulCentered
        (suzukiDF6D4EvenGalerkinSolveResidualInterval k j)).add
    (RationalInterval.sum Finset.univ fun r : Fin 300 =>
      (suzukiDF6D4EvenResidualColumnInterval (301 + r.val) i).mulCentered
        (suzukiDF6D4EvenResidualColumnInterval (301 + r.val) j))

theorem suzukiDF6D4EvenFiniteResidualGramEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenFiniteResidualGramEntryInterval i j).Contains
      (suzukiDF6D4EvenFiniteResidualGramEntry i j) := by
  exact RationalInterval.contains_add
    (RationalInterval.contains_sum fun k _ =>
      RationalInterval.contains_mulCentered
        (suzukiDF6D4EvenGalerkinSolveResidualInterval_contains k i)
        (suzukiDF6D4EvenGalerkinSolveResidualInterval_contains k j))
    (RationalInterval.contains_sum fun r _ =>
      RationalInterval.contains_mulCentered
        (suzukiDF6D4EvenResidualColumnInterval_contains (301 + r.val)
          (by omega) (by have := r.isLt; omega) i)
        (suzukiDF6D4EvenResidualColumnInterval_contains (301 + r.val)
          (by omega) (by have := r.isLt; omega) j))

def suzukiDF6D4OddFiniteResidualGramEntry (i j : Fin 44) : Real :=
  (∑ k : Fin 256,
      suzukiDF6D4OddGalerkinSolveResidual k i *
        suzukiDF6D4OddGalerkinSolveResidual k j) +
    ∑ r : Fin 300,
      suzukiDF6D4OddResidualColumn (301 + r.val) i *
        suzukiDF6D4OddResidualColumn (301 + r.val) j

def suzukiDF6D4OddFiniteResidualGramEntryInterval
    (i j : Fin 44) : RationalInterval :=
  (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      (suzukiDF6D4OddGalerkinSolveResidualInterval k i).mulCentered
        (suzukiDF6D4OddGalerkinSolveResidualInterval k j)).add
    (RationalInterval.sum Finset.univ fun r : Fin 300 =>
      (suzukiDF6D4OddResidualColumnInterval (301 + r.val) i).mulCentered
        (suzukiDF6D4OddResidualColumnInterval (301 + r.val) j))

theorem suzukiDF6D4OddFiniteResidualGramEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddFiniteResidualGramEntryInterval i j).Contains
      (suzukiDF6D4OddFiniteResidualGramEntry i j) := by
  exact RationalInterval.contains_add
    (RationalInterval.contains_sum fun k _ =>
      RationalInterval.contains_mulCentered
        (suzukiDF6D4OddGalerkinSolveResidualInterval_contains k i)
        (suzukiDF6D4OddGalerkinSolveResidualInterval_contains k j))
    (RationalInterval.contains_sum fun r _ =>
      RationalInterval.contains_mulCentered
        (suzukiDF6D4OddResidualColumnInterval_contains (301 + r.val)
          (by omega) (by have := r.isLt; omega) i)
        (suzukiDF6D4OddResidualColumnInterval_contains (301 + r.val)
          (by omega) (by have := r.isLt; omega) j))

end

end RiemannHypothesisProject.Experiments.M100
