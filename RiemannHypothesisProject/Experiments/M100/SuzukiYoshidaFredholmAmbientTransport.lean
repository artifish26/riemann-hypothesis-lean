import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmMeanCorrection

/-!
# M100-DF6F ambient Fredholm transport

Suzuki's Section 8 adjoint calculation tests against the zero-mean core but
keeps `S_a v` in ambient interval `L²`.  The constant component left by those
tests is the deficiency datum; it is normalized before the displayed
Fredholm equations.  This module separates that ambient-codomain operator
from its zero-mean compression and proves the exact projection bridge.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

local instance suzukiFredholmAmbientTransportCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- The screw-kernel operator restricted to zero-mean inputs while retaining
its ambient interval `L²` output. -/
def suzukiSourceAmbientGOperator (a : Real) :
    SuzukiFiniteIntervalZeroMeanL2 a →L[Complex]
      SuzukiFiniteIntervalL2 a :=
  (suzukiFiniteIntervalL2Operator suzukiScrewFunction
    continuous_suzukiScrewFunction a).comp
      (Submodule.subtypeL (SuzukiFiniteIntervalZeroMeanSubspace a))

/-- The checked translation-kernel representative of the inverse-Neumann
operator, restricted to zero-mean inputs with ambient output retained. -/
def suzukiSourceAmbientKOperator (a : Real) :
    SuzukiFiniteIntervalZeroMeanL2 a →L[Complex]
      SuzukiFiniteIntervalL2 a :=
  (suzukiFiniteIntervalL2Operator suzukiNeumannTranslationKernel
    continuous_suzukiNeumannTranslationKernel a).comp
      (Submodule.subtypeL (SuzukiFiniteIntervalZeroMeanSubspace a))

/-- Ambient-codomain representative of `G_a - lambda K_a`. -/
def suzukiSourceAmbientShiftedOperator (a lambda : Real) :
    SuzukiFiniteIntervalZeroMeanL2 a →L[Complex]
      SuzukiFiniteIntervalL2 a :=
  suzukiSourceAmbientGOperator a -
    (lambda : Complex) • suzukiSourceAmbientKOperator a

/-- The existing self-adjoint source operator is exactly the zero-mean
projection of the ambient-codomain operator. -/
theorem suzukiSourceShiftedOperator_eq_projection_comp_ambient
    (a lambda : Real) :
    suzukiSourceShiftedOperator a lambda =
      (suzukiFiniteIntervalZeroMeanProjection a).comp
        (suzukiSourceAmbientShiftedOperator a lambda) := by
  unfold suzukiSourceShiftedOperator suzukiSourceGOperator
    suzukiSourceKOperator suzukiFiniteIntervalZeroMeanCompression
    suzukiSourceAmbientShiftedOperator suzukiSourceAmbientGOperator
    suzukiSourceAmbientKOperator
  ext u
  simp

/-- An ambient plus Fredholm equation implies its compressed projected
equation.  This implication is the valid direction of the projection bridge.
-/
theorem suzukiSourceAmbientShiftedOperator_solve_plus_implies_projected
    {a lambda : Real} {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)) :
    suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmPlusForcing a := by
  rw [suzukiSourceShiftedOperator_eq_projection_comp_ambient]
  change suzukiFiniteIntervalZeroMeanProjection a
      (suzukiSourceAmbientShiftedOperator a lambda u) =
    suzukiFredholmPlusForcing a
  rw [hsolve]
  rfl

/-- An ambient minus Fredholm equation implies its compressed projected
equation. -/
theorem suzukiSourceAmbientShiftedOperator_solve_minus_implies_projected
    {a lambda : Real} {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)) :
    suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmMinusForcing a := by
  rw [suzukiSourceShiftedOperator_eq_projection_comp_ambient]
  change suzukiFiniteIntervalZeroMeanProjection a
      (suzukiSourceAmbientShiftedOperator a lambda u) =
    suzukiFredholmMinusForcing a
  rw [hsolve]
  rfl

/-- The compressed plus equation records precisely the projection of the
ambient equation, and therefore cannot recover its constant component. -/
theorem suzukiSourceShiftedOperator_solve_plus_iff_projected_ambient
    {a lambda : Real} {u : SuzukiFiniteIntervalZeroMeanL2 a} :
    suzukiSourceShiftedOperator a lambda u =
        suzukiFredholmPlusForcing a ↔
      suzukiFiniteIntervalZeroMeanProjection a
          (suzukiSourceAmbientShiftedOperator a lambda u) =
        suzukiFiniteIntervalZeroMeanProjection a
          (suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmPlusContinuous a)) := by
  rw [suzukiSourceShiftedOperator_eq_projection_comp_ambient]
  rfl

/-- The analogous exact statement for the minus equation. -/
theorem suzukiSourceShiftedOperator_solve_minus_iff_projected_ambient
    {a lambda : Real} {u : SuzukiFiniteIntervalZeroMeanL2 a} :
    suzukiSourceShiftedOperator a lambda u =
        suzukiFredholmMinusForcing a ↔
      suzukiFiniteIntervalZeroMeanProjection a
          (suzukiSourceAmbientShiftedOperator a lambda u) =
        suzukiFiniteIntervalZeroMeanProjection a
          (suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmMinusContinuous a)) := by
  rw [suzukiSourceShiftedOperator_eq_projection_comp_ambient]
  rfl

end

end RiemannHypothesisProject.Experiments.M100
