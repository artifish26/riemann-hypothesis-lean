import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceEnergyCompletion
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmL2Realization

/-!
# M100-DF6F source-energy realization receiver

This module connects an individually realizable source-energy completion
vector to the checked ambient Fredholm equations.  The three hard source
inputs remain separate: canonical-core membership, the smooth adjoint tests,
and the explicit complex mean.  No global completion-to-`L2` map is assumed.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- A realizable plus completion vector satisfying the source adjoint tests
and the explicit mean extracts to a literal interval-`L2` solution. -/
theorem suzukiSourceEnergyRealizedL2_ambient_plus
    {a : Real} (ha : 0 < a) {lambda : Real}
    (x : SuzukiSourceEnergyCompletion a ha)
    (hx : SuzukiSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda
      (suzukiSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceAmbientShiftedOperator a lambda
        (suzukiSourceEnergyRealizedL2 x hx) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a) :=
  (suzukiSourceAmbientShiftedOperator_eq_plus_iff_adjoint_and_explicitMean
    ha).2 ⟨hadjoint, hmean⟩

/-- Minus-sign realization receiver. -/
theorem suzukiSourceEnergyRealizedL2_ambient_minus
    {a : Real} (ha : 0 < a) {lambda : Real}
    (x : SuzukiSourceEnergyCompletion a ha)
    (hx : SuzukiSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda
      (suzukiSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceAmbientShiftedOperator a lambda
        (suzukiSourceEnergyRealizedL2 x hx) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a) :=
  (suzukiSourceAmbientShiftedOperator_eq_minus_iff_adjoint_and_explicitMean
    ha).2 ⟨hadjoint, hmean⟩

/-- The plus source data therefore inhabit the exact ambient existence
surface; the witness is the uniquely extracted interval-`L2` vector. -/
theorem exists_suzukiSourceAmbientShiftedOperator_eq_plus_of_energy
    {a : Real} (ha : 0 < a) {lambda : Real}
    (x : SuzukiSourceEnergyCompletion a ha)
    (hx : SuzukiSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda
      (suzukiSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    ∃ u : SuzukiFiniteIntervalZeroMeanL2 a,
      suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmPlusContinuous a) := by
  exact ⟨suzukiSourceEnergyRealizedL2 x hx,
    suzukiSourceEnergyRealizedL2_ambient_plus ha x hx hadjoint hmean⟩

/-- Minus source data inhabit the exact ambient existence surface. -/
theorem exists_suzukiSourceAmbientShiftedOperator_eq_minus_of_energy
    {a : Real} (ha : 0 < a) {lambda : Real}
    (x : SuzukiSourceEnergyCompletion a ha)
    (hx : SuzukiSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda
      (suzukiSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    ∃ u : SuzukiFiniteIntervalZeroMeanL2 a,
      suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmMinusContinuous a) := by
  exact ⟨suzukiSourceEnergyRealizedL2 x hx,
    suzukiSourceEnergyRealizedL2_ambient_minus ha x hx hadjoint hmean⟩

/-- Below the checked threshold, the extracted plus solution is the unique
literal interval-`L2` solution. -/
theorem suzukiDF6F_sourceEnergy_plus_solution_unique
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (x : SuzukiSourceEnergyCompletion a (suzukiDF6E_radius_pos ha))
    (hx : SuzukiSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda
      (suzukiSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hu : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)) :
    u = suzukiSourceEnergyRealizedL2 x hx := by
  apply suzukiDF6F_ambient_solution_unique
    hsource hequation25 ha hlambda
  rw [hu]
  exact (suzukiSourceEnergyRealizedL2_ambient_plus
    (suzukiDF6E_radius_pos ha) x hx hadjoint hmean).symm

/-- Below the checked threshold, the extracted minus solution is likewise the
unique literal interval-`L2` solution. -/
theorem suzukiDF6F_sourceEnergy_minus_solution_unique
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (x : SuzukiSourceEnergyCompletion a (suzukiDF6E_radius_pos ha))
    (hx : SuzukiSourceEnergyL2Realizable x)
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda
      (suzukiSourceEnergyRealizedL2 x hx)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiSourceEnergyRealizedL2 x hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hu : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)) :
    u = suzukiSourceEnergyRealizedL2 x hx := by
  apply suzukiDF6F_ambient_solution_unique
    hsource hequation25 ha hlambda
  rw [hu]
  exact (suzukiSourceEnergyRealizedL2_ambient_minus
    (suzukiDF6E_radius_pos ha) x hx hadjoint hmean).symm

end

end RiemannHypothesisProject.Experiments.M100
