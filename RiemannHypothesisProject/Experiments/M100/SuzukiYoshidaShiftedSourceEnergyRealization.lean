import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaShiftedSourceEnergyCompletion
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmL2Realization

/-!
# M100-DF6F shifted source-energy realization receiver

This module connects an individually realizable vector in Suzuki's actual
shifted completion `H(S_(a,lambda))` to the checked ambient Fredholm equations.
The source-form premise, equation (2.5), completion-core membership, smooth
adjoint tests, and explicit complex mean all remain visible.  No global map
from the shifted completion into interval `L2` is assumed.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- A realizable plus vector in `H(S_(a,lambda))`, together with the source
adjoint tests and explicit mean, extracts to a literal interval-`L2` solution. -/
theorem suzukiShiftedSourceEnergyRealizedL2_ambient_plus
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (hx : SuzukiShiftedSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda
      (suzukiShiftedSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceAmbientShiftedOperator a lambda
        (suzukiShiftedSourceEnergyRealizedL2 x hx) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a) :=
  (suzukiSourceAmbientShiftedOperator_eq_plus_iff_adjoint_and_explicitMean
    (suzukiDF6E_radius_pos ha)).2 ⟨hadjoint, hmean⟩

/-- Minus-sign shifted-completion realization receiver. -/
theorem suzukiShiftedSourceEnergyRealizedL2_ambient_minus
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (hx : SuzukiShiftedSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda
      (suzukiShiftedSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceAmbientShiftedOperator a lambda
        (suzukiShiftedSourceEnergyRealizedL2 x hx) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a) :=
  (suzukiSourceAmbientShiftedOperator_eq_minus_iff_adjoint_and_explicitMean
    (suzukiDF6E_radius_pos ha)).2 ⟨hadjoint, hmean⟩

/-- The plus source data inhabit the exact ambient existence surface, with the
unique shifted-energy-core representative as witness. -/
theorem exists_suzukiSourceAmbientShiftedOperator_eq_plus_of_shiftedEnergy
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (hx : SuzukiShiftedSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda
      (suzukiShiftedSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    ∃ u : SuzukiFiniteIntervalZeroMeanL2 a,
      suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmPlusContinuous a) := by
  exact ⟨suzukiShiftedSourceEnergyRealizedL2 x hx,
    suzukiShiftedSourceEnergyRealizedL2_ambient_plus
      hsource hequation25 ha hlambda x hx hadjoint hmean⟩

/-- Minus source data inhabit the exact ambient existence surface. -/
theorem exists_suzukiSourceAmbientShiftedOperator_eq_minus_of_shiftedEnergy
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (hx : SuzukiShiftedSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda
      (suzukiShiftedSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    ∃ u : SuzukiFiniteIntervalZeroMeanL2 a,
      suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmMinusContinuous a) := by
  exact ⟨suzukiShiftedSourceEnergyRealizedL2 x hx,
    suzukiShiftedSourceEnergyRealizedL2_ambient_minus
      hsource hequation25 ha hlambda x hx hadjoint hmean⟩

/-- Below the checked threshold, the extracted plus solution is the unique
literal interval-`L2` solution. -/
theorem suzukiDF6F_shiftedSourceEnergy_plus_solution_unique
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (hx : SuzukiShiftedSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda
      (suzukiShiftedSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hu : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)) :
    u = suzukiShiftedSourceEnergyRealizedL2 x hx := by
  apply suzukiDF6F_ambient_solution_unique
    hsource hequation25 ha hlambda
  rw [hu]
  exact (suzukiShiftedSourceEnergyRealizedL2_ambient_plus
    hsource hequation25 ha hlambda x hx hadjoint hmean).symm

/-- Below the checked threshold, the extracted minus solution is likewise the
unique literal interval-`L2` solution. -/
theorem suzukiDF6F_shiftedSourceEnergy_minus_solution_unique
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (hx : SuzukiShiftedSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda
      (suzukiShiftedSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hu : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)) :
    u = suzukiShiftedSourceEnergyRealizedL2 x hx := by
  apply suzukiDF6F_ambient_solution_unique
    hsource hequation25 ha hlambda
  rw [hu]
  exact (suzukiShiftedSourceEnergyRealizedL2_ambient_minus
    hsource hequation25 ha hlambda x hx hadjoint hmean).symm

end

end RiemannHypothesisProject.Experiments.M100
