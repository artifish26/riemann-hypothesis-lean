import RiemannHypothesisProject.Experiments.M100.SuzukiConcreteReflectionEquivariance
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaShiftedSourceEnergyVectorEndpoint

/-!
# M100-DF6F reflection obstruction to simultaneous L2 realization

The projected plus and minus forcing terms are related by reflection because
zero-mean compression removes their opposite imaginary constants.  The real
even ambient kernels commute with reflection.  Below the checked coercivity
threshold, uniqueness of the projected equation therefore makes the two
interval-`L2` solutions reflections of one another.  Their ambient output
means must then agree, whereas Suzuki's displayed normalizations have opposite
nonzero imaginary parts.  Consequently the two canonical shifted-completion
vectors cannot both be interval-`L2` realizable with those ambient means.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped InnerProductSpace

/-- Reflection fixes the constant-one vector on the symmetric interval. -/
theorem suzukiFiniteIntervalL2Reflection_one
    (a : Real) :
    suzukiFiniteIntervalL2Reflection a
        (suzukiFiniteIntervalOneComplexL2 a) =
      suzukiFiniteIntervalOneComplexL2 a := by
  rw [suzukiFiniteIntervalOneComplexL2,
    suzukiFiniteIntervalContinuousToL2_reflection]
  congr 1

/-- Reflection preserves the interval mean. -/
theorem suzukiFiniteIntervalMeanCLM_reflection
    (a : Real) (u : SuzukiFiniteIntervalL2 a) :
    suzukiFiniteIntervalMeanCLM a
        (suzukiFiniteIntervalL2Reflection a u) =
      suzukiFiniteIntervalMeanCLM a u := by
  rw [suzukiFiniteIntervalMeanCLM_apply,
    suzukiFiniteIntervalMeanCLM_apply]
  have h := (suzukiFiniteIntervalL2Reflection a).inner_map_map
    (suzukiFiniteIntervalOneComplexL2 a) u
  rwa [suzukiFiniteIntervalL2Reflection_one] at h

/-- Reflection restricted to the closed zero-mean source space. -/
def suzukiFiniteIntervalZeroMeanL2Reflection (a : Real) :
    SuzukiFiniteIntervalZeroMeanL2 a →ₗᵢ[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a where
  toFun u := ⟨suzukiFiniteIntervalL2Reflection a u, by
    rw [mem_suzukiFiniteIntervalZeroMeanSubspace,
      suzukiFiniteIntervalMeanCLM_reflection]
    exact u.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add (suzukiFiniteIntervalL2Reflection a)
      (u : SuzukiFiniteIntervalL2 a) (v : SuzukiFiniteIntervalL2 a)
  map_smul' c u := by
    apply Subtype.ext
    exact map_smul (suzukiFiniteIntervalL2Reflection a) c
      (u : SuzukiFiniteIntervalL2 a)
  norm_map' u := (suzukiFiniteIntervalL2Reflection a).norm_map u

@[simp]
theorem suzukiFiniteIntervalZeroMeanL2Reflection_coe
    (a : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    (suzukiFiniteIntervalZeroMeanL2Reflection a u :
        SuzukiFiniteIntervalL2 a) =
      suzukiFiniteIntervalL2Reflection a u :=
  rfl

/-- The ambient screw-kernel operator commutes with reflection. -/
theorem suzukiSourceAmbientGOperator_reflection
    (a : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    suzukiSourceAmbientGOperator a
        (suzukiFiniteIntervalZeroMeanL2Reflection a u) =
      suzukiFiniteIntervalL2Reflection a
        (suzukiSourceAmbientGOperator a u) := by
  exact suzukiFiniteIntervalL2Operator_reflection_of_even
    continuous_suzukiScrewFunction suzukiScrewFunction_neg a u

/-- The ambient inverse-Neumann translation representative commutes with
reflection. -/
theorem suzukiSourceAmbientKOperator_reflection
    (a : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    suzukiSourceAmbientKOperator a
        (suzukiFiniteIntervalZeroMeanL2Reflection a u) =
      suzukiFiniteIntervalL2Reflection a
        (suzukiSourceAmbientKOperator a u) := by
  exact suzukiFiniteIntervalL2Operator_reflection_of_even
    continuous_suzukiNeumannTranslationKernel
      suzukiNeumannTranslationKernel_neg a u

/-- Hence the real shifted ambient representative commutes with reflection. -/
theorem suzukiSourceAmbientShiftedOperator_reflection
    (a lambda : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    suzukiSourceAmbientShiftedOperator a lambda
        (suzukiFiniteIntervalZeroMeanL2Reflection a u) =
      suzukiFiniteIntervalL2Reflection a
        (suzukiSourceAmbientShiftedOperator a lambda u) := by
  change suzukiSourceAmbientGOperator a
        (suzukiFiniteIntervalZeroMeanL2Reflection a u) -
      (lambda : Complex) • suzukiSourceAmbientKOperator a
        (suzukiFiniteIntervalZeroMeanL2Reflection a u) =
      suzukiFiniteIntervalL2Reflection a
        (suzukiSourceAmbientGOperator a u -
          (lambda : Complex) • suzukiSourceAmbientKOperator a u)
  rw [suzukiSourceAmbientGOperator_reflection,
    suzukiSourceAmbientKOperator_reflection, map_sub, map_smul]

/-- Reflecting the literal plus right-hand side and then removing its constant
component gives the projected minus forcing. -/
theorem suzukiFiniteIntervalZeroMeanProjection_reflection_fredholmPlus
    (a : Real) :
    suzukiFiniteIntervalZeroMeanProjection a
        (suzukiFiniteIntervalL2Reflection a
          (suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmPlusContinuous a))) =
      suzukiFredholmMinusForcing a := by
  rw [suzukiFiniteIntervalContinuousToL2_reflection]
  change suzukiFiniteIntervalContinuousToZeroMeanL2 a
      (suzukiFiniteIntervalContinuousReflection a
        (suzukiFredholmPlusContinuous a)) =
    suzukiFiniteIntervalContinuousToZeroMeanL2 a
      (suzukiFredholmMinusContinuous a)
  have hreflect :
      suzukiFiniteIntervalContinuousReflection a
          (suzukiFredholmPlusContinuous a) =
        suzukiFredholmExponentialContinuous a (-1) +
          suzukiFiniteIntervalConstantContinuous a Complex.I := by
    ext x
    simp [suzukiFiniteIntervalContinuousReflection,
      suzukiFredholmPlusContinuous,
      suzukiFredholmExponentialContinuous,
      suzukiFiniteIntervalConstantContinuous,
      suzukiFiniteIntervalNeg]
  rw [hreflect]
  unfold suzukiFredholmMinusContinuous
  rw [map_add, map_sub,
    suzukiFiniteIntervalContinuousToZeroMeanL2_const_eq_zero,
    add_zero, sub_zero]

/-- The two source-normalized literal ambient equations cannot simultaneously
have zero-mean interval-`L2` solutions below the checked threshold. -/
theorem not_exists_suzukiDF6F_ambient_plus_and_minus_solutions
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real)) :
    ¬ (∃ uPlus uMinus : SuzukiFiniteIntervalZeroMeanL2 a,
        suzukiSourceAmbientShiftedOperator a lambda uPlus =
          suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmPlusContinuous a) ∧
        suzukiSourceAmbientShiftedOperator a lambda uMinus =
          suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmMinusContinuous a)) := by
  rintro ⟨uPlus, uMinus, hplus, hminus⟩
  have hprojectedMinus :
      suzukiSourceShiftedOperator a lambda
          (suzukiFiniteIntervalZeroMeanL2Reflection a uPlus) =
        suzukiFredholmMinusForcing a := by
    rw [suzukiSourceShiftedOperator_eq_projection_comp_ambient]
    change suzukiFiniteIntervalZeroMeanProjection a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiFiniteIntervalZeroMeanL2Reflection a uPlus)) = _
    rw [suzukiSourceAmbientShiftedOperator_reflection, hplus,
      suzukiFiniteIntervalZeroMeanProjection_reflection_fredholmPlus]
  have hprojectedMinus' :
      suzukiSourceShiftedOperator a lambda uMinus =
        suzukiFredholmMinusForcing a :=
    suzukiSourceAmbientShiftedOperator_solve_minus_implies_projected hminus
  have heq :
      suzukiFiniteIntervalZeroMeanL2Reflection a uPlus = uMinus := by
    apply sub_eq_zero.mp
    apply (suzukiSourceKSeminorm_definite_iff_injective
      (suzukiDF6E_radius_pos ha)).mpr
        (suzukiSourceKOperator_injective (suzukiDF6E_radius_pos ha))
    exact suzukiDF6F_shifted_solutions_sub_sourceKSeminorm_eq_zero
      hsource hequation25 ha hlambda
        (hprojectedMinus.trans hprojectedMinus'.symm)
  have hambientEq :
      suzukiFiniteIntervalL2Reflection a
          (suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmPlusContinuous a)) =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmMinusContinuous a) := by
    calc
      _ = suzukiSourceAmbientShiftedOperator a lambda
          (suzukiFiniteIntervalZeroMeanL2Reflection a uPlus) := by
            rw [suzukiSourceAmbientShiftedOperator_reflection, hplus]
      _ = suzukiSourceAmbientShiftedOperator a lambda uMinus := by rw [heq]
      _ = _ := hminus
  have hmean := congrArg (suzukiFiniteIntervalMeanCLM a) hambientEq
  rw [suzukiFiniteIntervalMeanCLM_reflection,
    suzukiFiniteIntervalMeanCLM_fredholmPlus_eq
      (suzukiDF6E_radius_pos ha),
    suzukiFiniteIntervalMeanCLM_fredholmMinus_eq
      (suzukiDF6E_radius_pos ha)] at hmean
  have him := congrArg Complex.im hmean
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im,
    Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero] at him
  linarith [suzukiDF6E_radius_pos ha]

/-- In particular, the four proposed canonical-vector source obligations—`L2`
realizability and Suzuki's explicit ambient mean for both signs—are jointly
inconsistent.  Any viable source endpoint must retain the deficiency vectors
in `H(S_(a,lambda))` and treat the constant normalization modulo the compressed
zero-mean range, rather than realize both displayed representatives in
interval `L2`. -/
theorem not_suzukiDF6FShiftedSourceEnergyVectors_both_realizable_and_normalized
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (hxPlus : SuzukiShiftedSourceEnergyL2Realizable
      (suzukiDF6FShiftedSourceEnergyPlusVector
        hsource hequation25 a ha lambda hlambda))
    (hmeanPlus : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2
            (suzukiDF6FShiftedSourceEnergyPlusVector
              hsource hequation25 a ha lambda hlambda) hxPlus)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I)
    (hxMinus : SuzukiShiftedSourceEnergyL2Realizable
      (suzukiDF6FShiftedSourceEnergyMinusVector
        hsource hequation25 a ha lambda hlambda))
    (hmeanMinus : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda
          (suzukiShiftedSourceEnergyRealizedL2
            (suzukiDF6FShiftedSourceEnergyMinusVector
              hsource hequation25 a ha lambda hlambda) hxMinus)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    False := by
  apply not_exists_suzukiDF6F_ambient_plus_and_minus_solutions
    hsource hequation25 ha hlambda
  refine ⟨suzukiShiftedSourceEnergyRealizedL2
      (suzukiDF6FShiftedSourceEnergyPlusVector
        hsource hequation25 a ha lambda hlambda) hxPlus,
    suzukiShiftedSourceEnergyRealizedL2
      (suzukiDF6FShiftedSourceEnergyMinusVector
        hsource hequation25 a ha lambda hlambda) hxMinus, ?_, ?_⟩
  · exact suzukiDF6FShiftedSourceEnergyPlusVector_ambient
      hsource hequation25 a ha lambda hlambda hxPlus hmeanPlus
  · exact suzukiDF6FShiftedSourceEnergyMinusVector_ambient
      hsource hequation25 a ha lambda hlambda hxMinus hmeanMinus

end

end RiemannHypothesisProject.Experiments.M100
