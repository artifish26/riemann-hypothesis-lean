import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmAdjointTransport
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceKInjectivity

/-!
# M100-DF6F interval-L2 Fredholm realization boundary

This module isolates the exact range condition left by Suzuki's energy-space
deficiency construction.  A literal ambient solution exists exactly when one
zero-mean interval `L2` vector solves the checked projected equation and has
the explicit source-selected output mean.  Coercivity also makes any two such
realizations equal in the inverse-Neumann source seminorm.  No existence or
source realization theorem is assumed; the separate source-operator
injectivity theorem upgrades energy uniqueness to literal `L2` uniqueness.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

local instance suzukiFredholmL2RealizationCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- A projected plus solution together with the explicit zero-mode scalar is
exactly an interval-`L2` realization of Suzuki's printed ambient equation. -/
theorem exists_suzukiSourceAmbientShiftedOperator_eq_plus_iff
    {a : Real} (ha : 0 < a) {lambda : Real} :
    (∃ u : SuzukiFiniteIntervalZeroMeanL2 a,
      suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmPlusContinuous a)) ↔
      ∃ u : SuzukiFiniteIntervalZeroMeanL2 a,
        suzukiSourceShiftedOperator a lambda u =
            suzukiFredholmPlusForcing a ∧
          suzukiFiniteIntervalMeanCLM a
              (suzukiSourceAmbientShiftedOperator a lambda u) =
            ((Real.exp a - Real.exp (-a) : Real) : Complex) +
              ((2 * a : Real) : Complex) * Complex.I := by
  constructor
  · rintro ⟨u, hambient⟩
    refine ⟨u,
      suzukiSourceAmbientShiftedOperator_solve_plus_implies_projected hambient,
      ?_⟩
    rw [hambient, suzukiFiniteIntervalMeanCLM_fredholmPlus_eq ha]
  · rintro ⟨u, hprojected, hmean⟩
    refine ⟨u, ?_⟩
    apply (suzukiSourceAmbientShiftedOperator_eq_plus_iff_adjoint_and_explicitMean
      ha).2
    refine ⟨?_, hmean⟩
    rw [suzukiSourceAmbientSmoothAdjointIdentityAt_iff_full ha]
    intro v
    have hprojection :
        suzukiFiniteIntervalZeroMeanProjection a
            (suzukiSourceAmbientShiftedOperator a lambda u) =
          suzukiFiniteIntervalZeroMeanProjection a
            (suzukiFiniteIntervalContinuousToL2 a
              (suzukiFredholmPlusContinuous a)) :=
      (suzukiSourceShiftedOperator_solve_plus_iff_projected_ambient).mp
        hprojected
    change inner Complex
      (suzukiSourceAmbientShiftedOperator a lambda u -
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmPlusContinuous a))
      (v : SuzukiFiniteIntervalL2 a) = 0
    calc
      inner Complex
          (suzukiSourceAmbientShiftedOperator a lambda u -
            suzukiFiniteIntervalContinuousToL2 a
              (suzukiFredholmPlusContinuous a))
          (v : SuzukiFiniteIntervalL2 a) =
          inner Complex
            (suzukiFiniteIntervalZeroMeanProjection a
              (suzukiSourceAmbientShiftedOperator a lambda u -
                suzukiFiniteIntervalContinuousToL2 a
                  (suzukiFredholmPlusContinuous a))) v :=
        (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right v _).symm
      _ = 0 := by rw [map_sub, hprojection, sub_self, inner_zero_left]

/-- The analogous exact realization criterion for the minus equation. -/
theorem exists_suzukiSourceAmbientShiftedOperator_eq_minus_iff
    {a : Real} (ha : 0 < a) {lambda : Real} :
    (∃ u : SuzukiFiniteIntervalZeroMeanL2 a,
      suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmMinusContinuous a)) ↔
      ∃ u : SuzukiFiniteIntervalZeroMeanL2 a,
        suzukiSourceShiftedOperator a lambda u =
            suzukiFredholmMinusForcing a ∧
          suzukiFiniteIntervalMeanCLM a
              (suzukiSourceAmbientShiftedOperator a lambda u) =
            ((Real.exp a - Real.exp (-a) : Real) : Complex) -
              ((2 * a : Real) : Complex) * Complex.I := by
  constructor
  · rintro ⟨u, hambient⟩
    refine ⟨u,
      suzukiSourceAmbientShiftedOperator_solve_minus_implies_projected hambient,
      ?_⟩
    rw [hambient, suzukiFiniteIntervalMeanCLM_fredholmMinus_eq ha]
  · rintro ⟨u, hprojected, hmean⟩
    refine ⟨u, ?_⟩
    apply (suzukiSourceAmbientShiftedOperator_eq_minus_iff_adjoint_and_explicitMean
      ha).2
    refine ⟨?_, hmean⟩
    rw [suzukiSourceAmbientSmoothAdjointIdentityAt_iff_full ha]
    intro v
    have hprojection :
        suzukiFiniteIntervalZeroMeanProjection a
            (suzukiSourceAmbientShiftedOperator a lambda u) =
          suzukiFiniteIntervalZeroMeanProjection a
            (suzukiFiniteIntervalContinuousToL2 a
              (suzukiFredholmMinusContinuous a)) :=
      (suzukiSourceShiftedOperator_solve_minus_iff_projected_ambient).mp
        hprojected
    change inner Complex
      (suzukiSourceAmbientShiftedOperator a lambda u -
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmMinusContinuous a))
      (v : SuzukiFiniteIntervalL2 a) = 0
    calc
      inner Complex
          (suzukiSourceAmbientShiftedOperator a lambda u -
            suzukiFiniteIntervalContinuousToL2 a
              (suzukiFredholmMinusContinuous a))
          (v : SuzukiFiniteIntervalL2 a) =
          inner Complex
            (suzukiFiniteIntervalZeroMeanProjection a
              (suzukiSourceAmbientShiftedOperator a lambda u -
                suzukiFiniteIntervalContinuousToL2 a
                  (suzukiFredholmMinusContinuous a))) v :=
        (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right v _).symm
      _ = 0 := by rw [map_sub, hprojection, sub_self, inner_zero_left]

/-- Below the checked coercivity threshold, two projected solutions have zero
difference in the inverse-Neumann source seminorm. -/
theorem suzukiDF6F_shifted_solutions_sub_sourceKSeminorm_eq_zero
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u v : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceShiftedOperator a lambda u =
      suzukiSourceShiftedOperator a lambda v) :
    suzukiSourceKSeminorm a (u - v) = 0 := by
  have hoperator : suzukiSourceShiftedOperator a lambda (u - v) = 0 := by
    rw [map_sub, hsolve, sub_self]
  have hcoercive := suzukiDF6F_interval_shifted_source_coercive
    hsource hequation25 ha lambda (u - v)
  rw [hoperator, inner_zero_left] at hcoercive
  simp only [Complex.zero_re] at hcoercive
  have hKnonneg := re_inner_suzukiSourceKOperator_nonneg
    (suzukiDF6E_radius_pos ha) (u - v)
  have hcoefficient : 0 < (1 / 400000 : Real) - lambda := by
    linarith
  have hKzero :
      (inner Complex (suzukiSourceKOperator a (u - v)) (u - v)).re = 0 := by
    nlinarith
  unfold suzukiSourceKSeminorm
  rw [hKzero, Real.sqrt_zero]

/-- Thus literal ambient solutions are unique in source energy. -/
theorem suzukiDF6F_ambient_solutions_sub_sourceKSeminorm_eq_zero
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u v : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiSourceAmbientShiftedOperator a lambda v) :
    suzukiSourceKSeminorm a (u - v) = 0 := by
  apply suzukiDF6F_shifted_solutions_sub_sourceKSeminorm_eq_zero
    hsource hequation25 ha hlambda
  rw [suzukiSourceShiftedOperator_eq_projection_comp_ambient]
  change suzukiFiniteIntervalZeroMeanProjection a
      (suzukiSourceAmbientShiftedOperator a lambda u) =
    suzukiFiniteIntervalZeroMeanProjection a
      (suzukiSourceAmbientShiftedOperator a lambda v)
  rw [hsolve]

/-- If the inverse-Neumann source seminorm is definite, the checked coercivity
upgrades energy uniqueness to literal interval-`L2` uniqueness. -/
theorem suzukiDF6F_ambient_solution_unique_of_sourceKSeminorm_definite
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (hdefinite : ∀ w : SuzukiFiniteIntervalZeroMeanL2 a,
      suzukiSourceKSeminorm a w = 0 → w = 0)
    {u v : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiSourceAmbientShiftedOperator a lambda v) :
    u = v := by
  apply sub_eq_zero.mp
  exact hdefinite (u - v)
    (suzukiDF6F_ambient_solutions_sub_sourceKSeminorm_eq_zero
      hsource hequation25 ha hlambda hsolve)

/-- Operator-theoretic form of the uniqueness boundary: injectivity of the
compressed inverse-Neumann operator upgrades the checked source-energy
uniqueness to literal interval-`L2` uniqueness. -/
theorem suzukiDF6F_ambient_solution_unique_of_sourceKOperator_injective
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (hinjective : Function.Injective (suzukiSourceKOperator a))
    {u v : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiSourceAmbientShiftedOperator a lambda v) :
    u = v := by
  apply suzukiDF6F_ambient_solution_unique_of_sourceKSeminorm_definite
    hsource hequation25 ha hlambda
  · exact (suzukiSourceKSeminorm_definite_iff_injective
      (suzukiDF6E_radius_pos ha)).mpr hinjective
  · exact hsolve

/-- Below the checked coercivity threshold, Suzuki's printed ambient
interval-`L2` equation has at most one zero-mean solution.  Source-operator
injectivity is supplied by the dense smooth differential core. -/
theorem suzukiDF6F_ambient_solution_unique
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u v : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceAmbientShiftedOperator a lambda u =
      suzukiSourceAmbientShiftedOperator a lambda v) :
    u = v :=
  suzukiDF6F_ambient_solution_unique_of_sourceKOperator_injective
    hsource hequation25 ha hlambda
    (suzukiSourceKOperator_injective (suzukiDF6E_radius_pos ha)) hsolve

end

end RiemannHypothesisProject.Experiments.M100
