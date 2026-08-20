import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaLocalizedWeilForm
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceFormPolarization

/-!
# M100-DF6F smooth-core Guinand--Weil source reduction

This module replaces the broad smooth-core `G_a` representation premise for
Suzuki's literal localized zero form by the precise source formula that must
be borrowed and normalized.  The source statement identifies the canonical
multiplicity-aware zero pairing with the complex polarization of Burnol's
literature-normalized Guinand--Weil residual on the four standard core
combinations.

Everything after that formula is already checked locally: equation (2.5)
identifies each residual diagonal with the project complete form, and the
existing polarization theorem identifies that form with the `G_a` pairing.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open SchwartzLineTestFunction
open scoped InnerProductSpace

/-- Complex polarization of the literature-normalized Guinand--Weil residual
on Suzuki's smooth source core.  Keeping the four residual evaluations visible
makes the remaining source theorem independent of the project corrected form
and of the screw-kernel operator. -/
def suzukiSourceSmoothCoreResidualPolarization
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) : Complex :=
  (4 : Complex)⁻¹ *
    ((guinandWeilBurnolLiteratureResidualSide
        (suzukiProjectBase
          (suzukiSmoothCoreLinearSubmoduleAsCore (u + v)).1) : Complex) -
      (guinandWeilBurnolLiteratureResidualSide
        (suzukiProjectBase
          (suzukiSmoothCoreLinearSubmoduleAsCore (u - v)).1) : Complex) -
      Complex.I *
        (guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase
            (suzukiSmoothCoreLinearSubmoduleAsCore
              (u + Complex.I • v)).1) : Complex) +
      Complex.I *
        (guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase
            (suzukiSmoothCoreLinearSubmoduleAsCore
              (u - Complex.I • v)).1) : Complex))

/-- Remaining source theorem on the smooth core: Suzuki's literal
multiplicity-aware zero pairing is the polarized Guinand--Weil residual in the
project's checked Fourier and zero-coordinate normalization. The pairing
arguments are reversed because Suzuki is linear first while the project form
uses Mathlib's conjugate-linear-first inner product convention. -/
def SuzukiSourceAaSmoothCoreGuinandWeilFormula : Prop :=
  ∀ u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
    suzukiSourceLocalizedWeilPairing suzukiProjectAStar
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar v)
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u) =
      suzukiSourceSmoothCoreResidualPolarization u v

/-- Equation (2.5) and the checked X14 normalization identify the polarized
literature residual with the project complete-form polarization. -/
theorem suzukiSourceSmoothCoreResidualPolarization_eq_completePolarization
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceSmoothCoreResidualPolarization u v =
      suzukiProjectNormalizedCompleteCorePolarization u v := by
  have hproject : SuzukiProjectCompleteFormNormalizationAt suzukiProjectAStar :=
    suzukiProjectCompleteFormNormalizationAt_of_screwIdentity
      (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar)
  have hplus :
      guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase
            (suzukiSmoothCoreLinearSubmoduleAsCore (u + v)).1) =
        suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore (u + v)) := by
    simpa using hproject suzukiProjectAStar_pos
      (suzukiSmoothCoreLinearSubmoduleAsCore (u + v))
  have hminus :
      guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase
            (suzukiSmoothCoreLinearSubmoduleAsCore (u - v)).1) =
        suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore (u - v)) := by
    simpa using hproject suzukiProjectAStar_pos
      (suzukiSmoothCoreLinearSubmoduleAsCore (u - v))
  have hiPlus :
      guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase
            (suzukiSmoothCoreLinearSubmoduleAsCore
              (u + Complex.I • v)).1) =
        suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore
            (u + Complex.I • v)) := by
    simpa using hproject suzukiProjectAStar_pos
      (suzukiSmoothCoreLinearSubmoduleAsCore (u + Complex.I • v))
  have hiMinus :
      guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase
            (suzukiSmoothCoreLinearSubmoduleAsCore
              (u - Complex.I • v)).1) =
        suzukiProjectNormalizedCompleteCoreForm
          (suzukiSmoothCoreLinearSubmoduleAsCore
            (u - Complex.I • v)) := by
    simpa using hproject suzukiProjectAStar_pos
      (suzukiSmoothCoreLinearSubmoduleAsCore (u - Complex.I • v))
  unfold suzukiSourceSmoothCoreResidualPolarization
  unfold suzukiProjectNormalizedCompleteCorePolarization
  rw [hplus, hminus, hiPlus, hiMinus]

/-- The precise smooth-core Guinand--Weil source theorem supplies the former
broad `G_a` representation premise for the literal localized zero form. -/
theorem suzukiSourceAaLocalizedWeilFormCoreGRepresentation_of_smoothCoreGuinandWeil
    (hformula : SuzukiSourceAaSmoothCoreGuinandWeilFormula) :
    SuzukiSourceAaLocalizedWeilFormCoreGRepresentation := by
  intro u v
  unfold suzukiSourceAaLocalizedWeilForm
  rw [suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply,
    suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply]
  calc
    suzukiSourceLocalizedWeilPairing suzukiProjectAStar
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar v)
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u) =
        suzukiSourceSmoothCoreResidualPolarization u v := hformula u v
    _ = suzukiProjectNormalizedCompleteCorePolarization u v :=
      suzukiSourceSmoothCoreResidualPolarization_eq_completePolarization u v
    _ = inner Complex
          (suzukiSourceGOperator suzukiProjectAStar
            (suzukiSmoothCoreDifferentialZeroMeanLinearMap
              suzukiProjectAStar_pos u))
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap
            suzukiProjectAStar_pos v) :=
      (inner_suzukiSourceGOperator_smoothCoreDifferential_eq_completePolarization
        (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar)
        suzukiProjectAStar_pos u v).symm

/-- Literal zero-form endpoint receiver with the source formula exposed in
place of the already reduced smooth-core `G_a` premise. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_smoothCoreGuinandWeil
    (A : SuzukiSourceAaOperator)
    (hsourceGraph : SuzukiSourceAaLocalizedWeilAssociatedRepresentation A)
    (hbounded : SuzukiSourceAaLocalizedWeilFormBounded)
    (hformula : SuzukiSourceAaSmoothCoreGuinandWeilFormula) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator :=
  sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_localizedWeilForm
    A hsourceGraph hbounded
      (suzukiSourceAaLocalizedWeilFormCoreGRepresentation_of_smoothCoreGuinandWeil
        hformula)

end

end RiemannHypothesisProject.Experiments.M100
