import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmUniformBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# M100-DF6F literal Fredholm-equation obstruction

Suzuki's printed Section 8 right-hand sides are not zero-mean on `[-a,a]`.
Consequently they cannot be literal values of the checked compressed source
operator, whose codomain is the closed zero-mean interval space.  This module
records that mismatch explicitly before any solution-existence construction.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiFredholmEquationFiniteMeasureOnCompacts (a : Real) :
    IsFiniteMeasureOnCompacts
      (volume : Measure (SuzukiFiniteInterval a)) := by
  rw [Measure.Subtype.volume_def]
  exact IsFiniteMeasureOnCompacts.comap' (volume : Measure Real)
    continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)

private theorem integrable_suzukiFredholmPlusContinuous
    (a : Real) : Integrable (fun x : SuzukiFiniteInterval a =>
      suzukiFredholmPlusContinuous a x) := by
  rw [← integrableOn_univ]
  exact (suzukiFredholmPlusContinuous a).continuous.continuousOn.integrableOn_compact
    isCompact_univ

private theorem integrable_suzukiFredholmMinusContinuous
    (a : Real) : Integrable (fun x : SuzukiFiniteInterval a =>
      suzukiFredholmMinusContinuous a x) := by
  rw [← integrableOn_univ]
  exact (suzukiFredholmMinusContinuous a).continuous.continuousOn.integrableOn_compact
    isCompact_univ

/-- The real part of the literal plus right-hand side has its expected exact
interval mean. -/
theorem integral_suzukiFredholmPlusContinuous_re
    {a : Real} (ha : 0 < a) :
    (∫ x : SuzukiFiniteInterval a,
      suzukiFredholmPlusContinuous a x ∂volume).re =
        Real.exp a - Real.exp (-a) := by
  calc
    (∫ x : SuzukiFiniteInterval a,
        suzukiFredholmPlusContinuous a x ∂volume).re =
        ∫ x : SuzukiFiniteInterval a,
          (suzukiFredholmPlusContinuous a x).re ∂volume := by
      exact (integral_re (integrable_suzukiFredholmPlusContinuous a)).symm
    _ = ∫ x : SuzukiFiniteInterval a, Real.exp x.1 ∂volume := by
      congr 1
      funext x
      simp [suzukiFredholmPlusContinuous,
        suzukiFredholmExponentialContinuous,
        suzukiFiniteIntervalConstantContinuous, Complex.exp_ofReal_re]
    _ = Real.exp a - Real.exp (-a) := by
      rw [show (∫ x : SuzukiFiniteInterval a, Real.exp x.1 ∂volume) =
          ∫ x in Set.Icc (-a) a, Real.exp x by
        exact MeasureTheory.integral_subtype measurableSet_Icc
          (fun x : Real => Real.exp x)]
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
      rw [intervalIntegral.integral_deriv_eq_sub']
      · simp
      · exact fun _ _ => Real.differentiableAt_exp
      · exact Real.continuous_exp.continuousOn

/-- The real part of the literal minus right-hand side has the same positive
mean, with the exponential endpoints reversed by the substitution `x ↦ -x`.
-/
theorem integral_suzukiFredholmMinusContinuous_re
    {a : Real} (ha : 0 < a) :
    (∫ x : SuzukiFiniteInterval a,
      suzukiFredholmMinusContinuous a x ∂volume).re =
        Real.exp a - Real.exp (-a) := by
  calc
    (∫ x : SuzukiFiniteInterval a,
        suzukiFredholmMinusContinuous a x ∂volume).re =
        ∫ x : SuzukiFiniteInterval a,
          (suzukiFredholmMinusContinuous a x).re ∂volume := by
      exact (integral_re (integrable_suzukiFredholmMinusContinuous a)).symm
    _ = ∫ x : SuzukiFiniteInterval a, Real.exp (-x.1) ∂volume := by
      congr 1
      funext x
      rw [show suzukiFredholmMinusContinuous a x =
          suzukiFredholmExponentialContinuous a (-1) x -
            suzukiFiniteIntervalConstantContinuous a Complex.I x by rfl]
      rw [suzukiFredholmExponentialContinuous_apply,
        suzukiFiniteIntervalConstantContinuous_apply,
        Complex.sub_re, Complex.I_re, sub_zero]
      norm_num
      rw [← Complex.ofReal_neg, Complex.exp_ofReal_re]
    _ = Real.exp a - Real.exp (-a) := by
      rw [show (∫ x : SuzukiFiniteInterval a, Real.exp (-x.1) ∂volume) =
          ∫ x in Set.Icc (-a) a, Real.exp (-x) by
        exact MeasureTheory.integral_subtype measurableSet_Icc
          (fun x : Real => Real.exp (-x))]
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
      have hderiv : deriv (fun x : Real => -Real.exp (-x)) =
          fun x : Real => Real.exp (-x) := by
        funext x
        convert (((Real.hasDerivAt_exp (-x)).comp x
          (hasDerivAt_neg x)).neg.deriv) using 1 <;>
          simp [Function.comp_def]
      rw [← hderiv]
      rw [intervalIntegral.integral_deriv_eq_sub]
      · ring_nf
      · intro x _
        fun_prop
      · rw [hderiv]
        exact (Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _

/-- The literal plus right-hand side is not in the zero-mean source space. -/
theorem suzukiFiniteIntervalMeanCLM_fredholmPlus_ne_zero
    {a : Real} (ha : 0 < a) :
    suzukiFiniteIntervalMeanCLM a
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)) ≠ 0 := by
  rw [suzukiFiniteIntervalMeanCLM_continuous]
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [integral_suzukiFredholmPlusContinuous_re ha] at hre
  have hpos : 0 < Real.exp a - Real.exp (-a) := by
    rw [sub_pos, Real.exp_lt_exp]
    linarith
  simpa using hpos.ne' hre

/-- The literal minus right-hand side is not in the zero-mean source space. -/
theorem suzukiFiniteIntervalMeanCLM_fredholmMinus_ne_zero
    {a : Real} (ha : 0 < a) :
    suzukiFiniteIntervalMeanCLM a
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)) ≠ 0 := by
  rw [suzukiFiniteIntervalMeanCLM_continuous]
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [integral_suzukiFredholmMinusContinuous_re ha] at hre
  have hpos : 0 < Real.exp a - Real.exp (-a) := by
    rw [sub_pos, Real.exp_lt_exp]
    linarith
  simpa using hpos.ne' hre

/-- No checked shifted source vector can satisfy Suzuki's literal unprojected
plus equation inside the current zero-mean operator model. -/
theorem suzukiSourceShiftedOperator_ne_literalFredholmPlus
    {a : Real} (ha : 0 < a) (lambda : Real)
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    (suzukiSourceShiftedOperator a lambda u :
        SuzukiFiniteIntervalL2 a) ≠
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a) := by
  intro heq
  have hmean := congrArg (suzukiFiniteIntervalMeanCLM a) heq
  have hleft : suzukiFiniteIntervalMeanCLM a
      (suzukiSourceShiftedOperator a lambda u :
        SuzukiFiniteIntervalL2 a) = 0 :=
    (suzukiSourceShiftedOperator a lambda u).2
  rw [hleft] at hmean
  exact suzukiFiniteIntervalMeanCLM_fredholmPlus_ne_zero ha hmean.symm

/-- No checked shifted source vector can satisfy Suzuki's literal unprojected
minus equation inside the current zero-mean operator model. -/
theorem suzukiSourceShiftedOperator_ne_literalFredholmMinus
    {a : Real} (ha : 0 < a) (lambda : Real)
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    (suzukiSourceShiftedOperator a lambda u :
        SuzukiFiniteIntervalL2 a) ≠
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a) := by
  intro heq
  have hmean := congrArg (suzukiFiniteIntervalMeanCLM a) heq
  have hleft : suzukiFiniteIntervalMeanCLM a
      (suzukiSourceShiftedOperator a lambda u :
        SuzukiFiniteIntervalL2 a) = 0 :=
    (suzukiSourceShiftedOperator a lambda u).2
  rw [hleft] at hmean
  exact suzukiFiniteIntervalMeanCLM_fredholmMinus_ne_zero ha hmean.symm

end

end RiemannHypothesisProject.Experiments.M100
