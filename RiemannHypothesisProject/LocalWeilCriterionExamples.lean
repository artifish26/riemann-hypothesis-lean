import RiemannHypothesisProject.LocalWeilCriterion
import RiemannHypothesisProject.FiniteZeroWindowExamples

/-!
# Local Weil criterion examples

This file gives concrete local positivity-criterion templates. The examples are
finite and deliberately modest, but they exercise the full local chain:

finite critical-height family
  -> finite local Weil criterion
  -> sum-of-squares positivity certificate
  -> `RHOn family`
-/

namespace RiemannHypothesisProject

/--
The finite index type attached to a finite set of real heights.
-/
abbrev HeightIndex (heights : Finset ℝ) := {t : ℝ // t ∈ heights}

/-- The finite height index type is finite. -/
@[reducible]
noncomputable def heightIndexFintype (heights : Finset ℝ) :
    Fintype (HeightIndex heights) :=
  Fintype.ofFinset heights (by intro t; simp)

/--
A concrete finite local criterion for a finite critical-height family.

The quadratic form is the sum of squares on functions indexed by the chosen
heights. The local implication is supplied by the finite height-window
certificate from `FiniteZeroWindowExamples`.
-/
noncomputable def finiteCriticalSumSquaresLocalCriterion
    (heights : Finset ℝ) :
    FiniteLocalWeilCriterion (finiteCriticalFamily heights) where
  Index := HeightIndex heights
  indexFintype := heightIndexFintype heights
  quadraticForm := sumSquaresQuadraticForm
  positivity_implies_RHOn := fun _ => RHOn_finiteCriticalFamily heights

/--
The finite critical-height criterion is certified by the checked sum-of-squares
positivity model.
-/
noncomputable def finiteCriticalCertifiedSumSquaresLocalCriterion
    (heights : Finset ℝ) :
    CertifiedFiniteLocalWeilCriterion (finiteCriticalFamily heights) :=
  CertifiedFiniteLocalWeilCriterion.of_sumSquares
    (finiteCriticalSumSquaresLocalCriterion heights)
    (HeightIndex heights)
    (fun f => f)
    (by intro f; rfl)

/--
The certified finite local criterion proves RH on the finite critical-height
family.
-/
theorem RHOn_finiteCriticalFamily_from_sumSquaresCriterion
    (heights : Finset ℝ) :
    RHOn (finiteCriticalFamily heights) :=
  (finiteCriticalCertifiedSumSquaresLocalCriterion heights).RHOn

end RiemannHypothesisProject
