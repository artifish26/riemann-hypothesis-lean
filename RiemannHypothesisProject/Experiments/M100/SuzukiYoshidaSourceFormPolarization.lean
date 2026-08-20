import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaDifferentialCoreDensity

/-!
# M100-DF6F polarized source-form bridge

Suzuki's equation-(2.5) premise is stated as a quadratic identity on smooth
compactly supported primitives.  This module polarizes that identity and
identifies the full sesquilinear pairing of the compressed screw operator on
smooth differentials.  It is the checked core-level content of the formal
factorization `B_a = D* G_a D`; it does not construct `D*`, an unbounded
operator domain, or the Friedrichs extension.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped InnerProductSpace

/-- Complex polarization of the project-normalized complete quadratic form
at an arbitrary positive source radius. -/
def suzukiProjectNormalizedCompleteCorePolarization
    {a : Real} (u v : SuzukiSmoothCoreLinearSubmodule a) : Complex :=
  (4 : Complex)⁻¹ *
    ((suzukiProjectNormalizedCompleteCoreForm
        (suzukiSmoothCoreLinearSubmoduleAsCore (u + v)) : Complex) -
      (suzukiProjectNormalizedCompleteCoreForm
        (suzukiSmoothCoreLinearSubmoduleAsCore (u - v)) : Complex) -
      Complex.I *
        (suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore
            (u + Complex.I • v)) : Complex) +
      Complex.I *
        (suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore
            (u - Complex.I • v)) : Complex))

/-- Equation (2.5), together with linearity of the smooth differential,
identifies every polarized `G_a` pairing on the source core. -/
theorem inner_suzukiSourceGOperator_smoothCoreDifferential_eq_completePolarization
    {a : Real} (hsource : SuzukiEquation25SourceIdentityAt a)
    (ha : 0 < a) (u v : SuzukiSmoothCoreLinearSubmodule a) :
    inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v) =
      suzukiProjectNormalizedCompleteCorePolarization u v := by
  have hplus :=
    inner_suzukiSourceGOperator_smoothCoreDifferential_eq_completeForm
      hsource ha (suzukiSmoothCoreLinearSubmoduleAsCore (u + v))
  have hminus :=
    inner_suzukiSourceGOperator_smoothCoreDifferential_eq_completeForm
      hsource ha (suzukiSmoothCoreLinearSubmoduleAsCore (u - v))
  have hiPlus :=
    inner_suzukiSourceGOperator_smoothCoreDifferential_eq_completeForm
      hsource ha
        (suzukiSmoothCoreLinearSubmoduleAsCore (u + Complex.I • v))
  have hiMinus :=
    inner_suzukiSourceGOperator_smoothCoreDifferential_eq_completeForm
      hsource ha
        (suzukiSmoothCoreLinearSubmoduleAsCore (u - Complex.I • v))
  change
    inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha (u + v)))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha (u + v)) = _
      at hplus
  change
    inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha (u - v)))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha (u - v)) = _
      at hminus
  change
    inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha
            (u + Complex.I • v)))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha
          (u + Complex.I • v)) = _
      at hiPlus
  change
    inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha
            (u - Complex.I • v)))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha
          (u - Complex.I • v)) = _
      at hiMinus
  change
    inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v) = _
  have hpolar := inner_map_polarization'
    (suzukiSourceGOperator a).toLinearMap
    (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u)
    (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v)
  change
    inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v) = _ at hpolar
  have hcoe (w : SuzukiFiniteIntervalZeroMeanL2 a) :
      (suzukiSourceGOperator a).toLinearMap w =
        suzukiSourceGOperator a w := by
    rfl
  have hplus' :
      inner Complex
          ((suzukiSourceGOperator a).toLinearMap
            (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u +
              suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v))
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u +
            suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v) =
        (suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore (u + v)) : Complex) := by
    simpa only [map_add, hcoe] using hplus
  have hminus' :
      inner Complex
          ((suzukiSourceGOperator a).toLinearMap
            (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u -
              suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v))
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u -
            suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v) =
        (suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore (u - v)) : Complex) := by
    simpa only [map_sub, hcoe] using hminus
  have hiPlus' :
      inner Complex
          ((suzukiSourceGOperator a).toLinearMap
            (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u +
              Complex.I •
                suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v))
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u +
            Complex.I •
              suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v) =
        (suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore
            (u + Complex.I • v)) : Complex) := by
    simpa only [map_add, map_smul, hcoe] using hiPlus
  have hiMinus' :
      inner Complex
          ((suzukiSourceGOperator a).toLinearMap
            (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u -
              Complex.I •
                suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v))
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha u -
            Complex.I •
              suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v) =
        (suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore
            (u - Complex.I • v)) : Complex) := by
    simpa only [map_sub, map_smul, hcoe] using hiMinus
  rw [hpolar]
  unfold suzukiProjectNormalizedCompleteCorePolarization
  rw [hplus', hminus', hiPlus', hiMinus']
  ring

/-- At the frozen endpoint, the arbitrary-radius polarization is definitionally
the corrected-form polarization already used by the DF6D5 coordinate track. -/
theorem suzukiProjectNormalizedCompleteCorePolarization_eq_endpoint
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiProjectNormalizedCompleteCorePolarization u v =
      suzukiProjectNormalizedCompleteCorePolarizedForm u v := by
  rfl

/-- Endpoint core identification of the formal `D* G_a D` pairing with the
checked corrected closed form.  This is still a smooth-core theorem, not the
Friedrichs representation on the full operator domain. -/
theorem inner_suzukiSourceGOperator_differentials_eq_correctedCompleteForm
    (hsource : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    inner Complex
        (suzukiSourceGOperator suzukiProjectAStar
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap
            suzukiProjectAStar_pos u))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap
          suzukiProjectAStar_pos v) =
      suzukiYoshidaCorrectedCompleteForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) := by
  calc
    inner Complex
        (suzukiSourceGOperator suzukiProjectAStar
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap
            suzukiProjectAStar_pos u))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap
          suzukiProjectAStar_pos v) =
        suzukiProjectNormalizedCompleteCorePolarization u v :=
      inner_suzukiSourceGOperator_smoothCoreDifferential_eq_completePolarization
        hsource suzukiProjectAStar_pos u v
    _ = suzukiProjectNormalizedCompleteCorePolarizedForm u v :=
      suzukiProjectNormalizedCompleteCorePolarization_eq_endpoint u v
    _ = suzukiYoshidaCorrectedCompleteForm
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar u)
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar v) :=
      (suzukiYoshidaCorrectedCompleteForm_core_polarized u v).symm

end

end RiemannHypothesisProject.Experiments.M100
