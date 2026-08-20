import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaShiftedSourceEnergyVectors
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmL2Realization

/-!
# M100-DF6F canonical shifted-vector realization endpoint

The canonical Riesz vectors already satisfy the weak shifted equations.  If
one lies in the interval-`L2` core image, the weak equation gives the projected
Fredholm equation automatically.  The checked ambient realization criterion
then needs only the explicit complex mean.  Thus no separate smooth-adjoint
premise is required for these canonical vectors.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- A projected plus solution with the explicit mean satisfies the literal
ambient equation.  Coercive uniqueness identifies the witness produced by the
existing existence criterion with the supplied projected solution. -/
theorem suzukiSourceAmbientShiftedOperator_eq_plus_of_projected_and_mean
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (u : SuzukiFiniteIntervalZeroMeanL2 a)
    (hprojected : suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmPlusForcing a)
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda u) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a) := by
  rcases (exists_suzukiSourceAmbientShiftedOperator_eq_plus_iff
    (suzukiDF6E_radius_pos ha)).2 ⟨u, hprojected, hmean⟩ with ⟨v, hv⟩
  have hvprojected : suzukiSourceShiftedOperator a lambda v =
      suzukiFredholmPlusForcing a :=
    suzukiSourceAmbientShiftedOperator_solve_plus_implies_projected hv
  have hseminorm : suzukiSourceKSeminorm a (v - u) = 0 :=
    suzukiDF6F_shifted_solutions_sub_sourceKSeminorm_eq_zero
      hsource hequation25 ha hlambda (by rw [hvprojected, hprojected])
  have hvu : v = u := by
    apply sub_eq_zero.mp
    exact suzukiSourceKSeminorm_definite
      (suzukiDF6E_radius_pos ha) (v - u) hseminorm
  simpa [hvu] using hv

/-- Minus-sign counterpart. -/
theorem suzukiSourceAmbientShiftedOperator_eq_minus_of_projected_and_mean
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (u : SuzukiFiniteIntervalZeroMeanL2 a)
    (hprojected : suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmMinusForcing a)
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda u) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a) := by
  rcases (exists_suzukiSourceAmbientShiftedOperator_eq_minus_iff
    (suzukiDF6E_radius_pos ha)).2 ⟨u, hprojected, hmean⟩ with ⟨v, hv⟩
  have hvprojected : suzukiSourceShiftedOperator a lambda v =
      suzukiFredholmMinusForcing a :=
    suzukiSourceAmbientShiftedOperator_solve_minus_implies_projected hv
  have hseminorm : suzukiSourceKSeminorm a (v - u) = 0 :=
    suzukiDF6F_shifted_solutions_sub_sourceKSeminorm_eq_zero
      hsource hequation25 ha hlambda (by rw [hvprojected, hprojected])
  have hvu : v = u := by
    apply sub_eq_zero.mp
    exact suzukiSourceKSeminorm_definite
      (suzukiDF6E_radius_pos ha) (v - u) hseminorm
  simpa [hvu] using hv

/-- The canonical plus vector therefore satisfies Suzuki's literal ambient
equation once its two genuinely source-side properties—individual `L2`
realizability and the explicit mean—are supplied. -/
theorem suzukiDF6FShiftedSourceEnergyPlusVector_ambient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (hx : SuzukiShiftedSourceEnergyL2Realizable
      (suzukiDF6FShiftedSourceEnergyPlusVector
        hsource hequation25 a ha lambda hlambda))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2
            (suzukiDF6FShiftedSourceEnergyPlusVector
              hsource hequation25 a ha lambda hlambda) hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceAmbientShiftedOperator a lambda
        (suzukiShiftedSourceEnergyRealizedL2
          (suzukiDF6FShiftedSourceEnergyPlusVector
            hsource hequation25 a ha lambda hlambda) hx) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a) := by
  apply suzukiSourceAmbientShiftedOperator_eq_plus_of_projected_and_mean
    hsource hequation25 ha hlambda _
  · exact suzukiDF6FShiftedSourceEnergyPlusVector_projected_of_realizable
      hsource hequation25 a ha lambda hlambda hx
  · exact hmean

/-- Canonical minus-vector ambient endpoint. -/
theorem suzukiDF6FShiftedSourceEnergyMinusVector_ambient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (hx : SuzukiShiftedSourceEnergyL2Realizable
      (suzukiDF6FShiftedSourceEnergyMinusVector
        hsource hequation25 a ha lambda hlambda))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2
            (suzukiDF6FShiftedSourceEnergyMinusVector
              hsource hequation25 a ha lambda hlambda) hx)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceAmbientShiftedOperator a lambda
        (suzukiShiftedSourceEnergyRealizedL2
          (suzukiDF6FShiftedSourceEnergyMinusVector
            hsource hequation25 a ha lambda hlambda) hx) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a) := by
  apply suzukiSourceAmbientShiftedOperator_eq_minus_of_projected_and_mean
    hsource hequation25 ha hlambda _
  · exact suzukiDF6FShiftedSourceEnergyMinusVector_projected_of_realizable
      hsource hequation25 a ha lambda hlambda hx
  · exact hmean

end

end RiemannHypothesisProject.Experiments.M100
