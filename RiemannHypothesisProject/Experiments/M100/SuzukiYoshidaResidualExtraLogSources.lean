import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaExtraLogDomain
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaComparisonEnergyTrialSolve

/-!
# B3R-E fixed residual sources have one extra logarithm

This module instantiates the endpoint-mode theorem for the exact low modes and
the frozen rational Galerkin trial vectors used in the even and odd B3R-E
residual rows.  It does not yet construct the ambient `L²` residual
functionals.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

/-- The complete-form low source in an even B3R-E residual row. -/
def suzukiDF6D5B3REEvenLowSourceL2 (i : Fin 45) : SuzukiL2 :=
  suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos
    (suzukiDF6D4EvenLowMode i)

/-- The complete-form low source in an odd B3R-E residual row. -/
def suzukiDF6D5B3REOddLowSourceL2 (i : Fin 44) : SuzukiL2 :=
  suzukiYoshidaOddL2 suzukiProjectAStar suzukiProjectAStar_pos
    (suzukiDF6D4OddLowMode i)

/-- The frozen even comparison-energy Galerkin trial vector for one low row. -/
def suzukiDF6D5B3REEvenGalerkinTrialL2 (i : Fin 45) : SuzukiL2 :=
  ∑ k : Fin 256,
    ((suzukiDF6D4EvenGalerkinApproximant k i : Real) : Complex) •
      suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos
        (suzukiDF6D4GalerkinMode k)

/-- The frozen odd comparison-energy Galerkin trial vector for one low row. -/
def suzukiDF6D5B3REOddGalerkinTrialL2 (i : Fin 44) : SuzukiL2 :=
  ∑ k : Fin 256,
    ((suzukiDF6D4OddGalerkinApproximant k i : Real) : Complex) •
      suzukiYoshidaOddL2 suzukiProjectAStar suzukiProjectAStar_pos
        (suzukiDF6D4GalerkinMode k)

/-- Every even low source used by the complete cross block has the additional
logarithmic multiplier required for ambient `L²` pairing. -/
theorem suzukiDF6D5B3REEvenLowSourceL2_mem_extraLogFourierDomain
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) :
    SuzukiExtraLogFourierDomain (suzukiDF6D5B3REEvenLowSourceL2 i) := by
  exact suzukiYoshidaEvenL2_mem_extraLogFourierDomain hsource
    suzukiProjectAStar_pos (suzukiDF6D4EvenLowMode i)

/-- Odd counterpart for the complete cross block. -/
theorem suzukiDF6D5B3REOddLowSourceL2_mem_extraLogFourierDomain
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) :
    SuzukiExtraLogFourierDomain (suzukiDF6D5B3REOddLowSourceL2 i) := by
  exact suzukiYoshidaOddL2_mem_extraLogFourierDomain hsource
    suzukiProjectAStar_pos (suzukiDF6D4OddLowMode i)

/-- Every exact frozen even Galerkin trial vector is in the one-extra-log
domain. -/
theorem suzukiDF6D5B3REEvenGalerkinTrialL2_mem_extraLogFourierDomain
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) :
    SuzukiExtraLogFourierDomain (suzukiDF6D5B3REEvenGalerkinTrialL2 i) := by
  change suzukiDF6D5B3REEvenGalerkinTrialL2 i ∈
    SuzukiExtraLogFourierSubmodule
  unfold suzukiDF6D5B3REEvenGalerkinTrialL2
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _
      (suzukiYoshidaEvenL2_mem_extraLogFourierDomain hsource
        suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))

/-- Every exact frozen odd Galerkin trial vector is in the one-extra-log
domain. -/
theorem suzukiDF6D5B3REOddGalerkinTrialL2_mem_extraLogFourierDomain
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) :
    SuzukiExtraLogFourierDomain (suzukiDF6D5B3REOddGalerkinTrialL2 i) := by
  change suzukiDF6D5B3REOddGalerkinTrialL2 i ∈
    SuzukiExtraLogFourierSubmodule
  unfold suzukiDF6D5B3REOddGalerkinTrialL2
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _
      (suzukiYoshidaOddL2_mem_extraLogFourierDomain hsource
        suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))

/-- Both fixed vectors occurring in an even residual row satisfy the exact
one-extra-log domain condition. -/
theorem suzukiDF6D5B3REEvenResidualSources_mem_extraLogFourierDomain
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) :
    SuzukiExtraLogFourierDomain (suzukiDF6D5B3REEvenLowSourceL2 i) ∧
      SuzukiExtraLogFourierDomain
        (suzukiDF6D5B3REEvenGalerkinTrialL2 i) :=
  ⟨suzukiDF6D5B3REEvenLowSourceL2_mem_extraLogFourierDomain hsource i,
    suzukiDF6D5B3REEvenGalerkinTrialL2_mem_extraLogFourierDomain hsource i⟩

/-- Both fixed vectors occurring in an odd residual row satisfy the exact
one-extra-log domain condition. -/
theorem suzukiDF6D5B3REOddResidualSources_mem_extraLogFourierDomain
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) :
    SuzukiExtraLogFourierDomain (suzukiDF6D5B3REOddLowSourceL2 i) ∧
      SuzukiExtraLogFourierDomain
        (suzukiDF6D5B3REOddGalerkinTrialL2 i) :=
  ⟨suzukiDF6D5B3REOddLowSourceL2_mem_extraLogFourierDomain hsource i,
    suzukiDF6D5B3REOddGalerkinTrialL2_mem_extraLogFourierDomain hsource i⟩

end

end RiemannHypothesisProject.Experiments.M100
