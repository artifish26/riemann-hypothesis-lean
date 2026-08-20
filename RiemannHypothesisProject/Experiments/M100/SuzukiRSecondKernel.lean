import RiemannHypothesisProject.Experiments.M100.SuzukiFiniteIntervalL2Operator
import RiemannHypothesisProject.Experiments.M100.SuzukiLogRadiusCompletion
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.KernelNormalization
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# M100-DF6D2 Suzuki r-second kernel

This module removes the apparent singularity in Suzuki's displayed `r₁''`
formula, proves continuity of the resulting exact real kernel, and instantiates
the finite-interval `L²` operator constructed in the preceding subpass.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Filter Set MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace Topology

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiRSecondFiniteIntervalIsFiniteMeasureOnCompacts (a : Real) :
    IsFiniteMeasureOnCompacts
      (volume : Measure (SuzukiFiniteInterval a)) := by
  rw [Measure.Subtype.volume_def]
  exact IsFiniteMeasureOnCompacts.comap' (volume : Measure Real)
    continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)

/-- Suzuki's displayed off-origin formula for `r₁''`. -/
def suzukiR1SecondOffOrigin (x : Real) : Real :=
  Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) - 1 / (2 * x)

/-- A form of the same quotient adapted to the removable endpoint. -/
def suzukiR1SecondNormalized (t : Real) : Real :=
  Real.exp (3 * t / 4) / (Real.exp t - 1) - 1 / t

private theorem tendsto_suzukiExpRatio_nhdsGT_zero :
    Tendsto
      (fun t : Real =>
        (Real.exp (3 * t / 4) - 1) / (Real.exp t - 1))
      (nhdsWithin 0 (Ioi 0)) (nhds (3 / 4 : Real)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
  · filter_upwards with t
    have hlinear : HasDerivAt (fun x : Real => 3 * x / 4) (3 / 4) t := by
      simpa using ((hasDerivAt_id t).const_mul 3).div_const 4
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_exp (3 * t / 4)).comp t hlinear).sub_const 1
  · filter_upwards with t
    simpa using (Real.hasDerivAt_exp t).sub_const 1
  · filter_upwards with t
    exact Real.exp_ne_zero t
  · have hcontinuous : Continuous
        (fun t : Real => Real.exp (3 * t / 4) - 1) := by
      fun_prop
    simpa using tendsto_nhdsWithin_of_tendsto_nhds
      (hcontinuous.tendsto 0)
  · have hcontinuous : Continuous (fun t : Real => Real.exp t - 1) := by
      fun_prop
    simpa using tendsto_nhdsWithin_of_tendsto_nhds
      (hcontinuous.tendsto 0)
  · have hcontinuous : Continuous
        (fun t : Real =>
          (Real.exp (3 * t / 4) * (3 / 4)) / Real.exp t) := by
      have hnum : Continuous
          (fun t : Real => Real.exp (3 * t / 4) * (3 / 4)) := by
        fun_prop
      exact hnum.div Real.continuous_exp (fun t => Real.exp_ne_zero t)
    simpa using tendsto_nhdsWithin_of_tendsto_nhds
      (hcontinuous.tendsto 0)

private theorem tendsto_suzukiBinetPart_nhdsGT_zero :
    Tendsto
      (fun t : Real => 1 / (Real.exp t - 1) - 1 / t)
      (nhdsWithin 0 (Ioi 0)) (nhds (-1 / 2 : Real)) := by
  have h :=
    ComplexCompactExhaustion.tendsto_bennettGammaBinetKernel_real_nhdsGT_zero
      |>.sub_const (1 / 2 : Real)
  convert h using 1
  · funext t
    ring_nf
  · ring_nf

private theorem tendsto_suzukiR1SecondNormalized_nhdsGT_zero :
    Tendsto suzukiR1SecondNormalized
      (nhdsWithin 0 (Ioi 0)) (nhds (1 / 4 : Real)) := by
  have hsum := tendsto_suzukiBinetPart_nhdsGT_zero.add
    tendsto_suzukiExpRatio_nhdsGT_zero
  rw [show suzukiR1SecondNormalized = fun t : Real =>
      (1 / (Real.exp t - 1) - 1 / t) +
        (Real.exp (3 * t / 4) - 1) / (Real.exp t - 1) by
    funext t
    unfold suzukiR1SecondNormalized
    ring]
  convert hsum using 1
  norm_num

theorem suzukiR1SecondOffOrigin_eq_normalized (x : Real) (hx : x ≠ 0) :
    suzukiR1SecondOffOrigin x = suzukiR1SecondNormalized (2 * x) := by
  have hexpNeg : Real.exp (-2 * x) ≠ 0 := Real.exp_ne_zero _
  have hexpPos : Real.exp (2 * x) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hzero : 2 * x = 0 := Real.exp_injective (by
      simpa only [Real.exp_zero] using h)
    exact hx (by nlinarith)
  have hprod :
      Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hthree :
      Real.exp (-x / 2) * Real.exp (2 * x) =
        Real.exp (3 * (2 * x) / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdenom :
      1 - Real.exp (-2 * x) =
        Real.exp (-2 * x) * (Real.exp (2 * x) - 1) := by
    nlinarith [hprod]
  have hfactor :
      Real.exp (-x / 2) = Real.exp (-2 * x) *
        Real.exp (3 * (2 * x) / 4) := by
    calc
      Real.exp (-x / 2) = Real.exp (-x / 2) * 1 := by ring
      _ = Real.exp (-x / 2) *
          (Real.exp (-2 * x) * Real.exp (2 * x)) := by rw [hprod]
      _ = Real.exp (-2 * x) *
          (Real.exp (-x / 2) * Real.exp (2 * x)) := by ring
      _ = Real.exp (-2 * x) *
          Real.exp (3 * (2 * x) / 4) := by rw [hthree]
  unfold suzukiR1SecondOffOrigin suzukiR1SecondNormalized
  rw [hdenom, hfactor]
  field_simp [hx, hexpNeg, hexpPos]

theorem tendsto_suzukiR1SecondOffOrigin_nhdsGT_zero :
    Tendsto suzukiR1SecondOffOrigin
      (nhdsWithin 0 (Ioi 0)) (nhds (1 / 4 : Real)) := by
  have hscale :
      Tendsto (fun x : Real => 2 * x)
        (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    have hid : Tendsto (fun x : Real => x)
        (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := tendsto_id
    simpa only [mul_zero] using
      (Filter.TendstoNhdsWithinIoi.const_mul
        (b := (2 : Real)) (c := (0 : Real))
        (by norm_num : (0 : Real) < 2) hid)
  apply (tendsto_suzukiR1SecondNormalized_nhdsGT_zero.comp hscale).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (suzukiR1SecondOffOrigin_eq_normalized x hx.ne').symm

/-- The removable extension of Suzuki's `r₁''`, with source value `1/4`
at the origin. -/
def suzukiR1SecondKernel (t : Real) : Real :=
  if t = 0 then 1 / 4 else suzukiR1SecondOffOrigin |t|

@[simp]
theorem suzukiR1SecondKernel_zero :
    suzukiR1SecondKernel 0 = 1 / 4 := by
  simp [suzukiR1SecondKernel]

theorem continuous_suzukiR1SecondKernel :
    Continuous suzukiR1SecondKernel := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · subst t
    rw [continuousAt_iff_punctured_nhds]
    rw [suzukiR1SecondKernel_zero]
    have habs : Tendsto (fun x : Real => |x|)
        (nhdsWithin 0 ({0} : Set Real)ᶜ) (nhdsWithin 0 (Ioi 0)) :=
      tendsto_abs_nhdsNE_zero
    have hlimit := tendsto_suzukiR1SecondOffOrigin_nhdsGT_zero.comp habs
    apply hlimit.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hx
    simp [suzukiR1SecondKernel, hx0]
  · have habs : |t| ≠ 0 := abs_ne_zero.mpr ht
    have hden : 1 - Real.exp (-2 * |t|) ≠ 0 := by
      rw [sub_ne_zero]
      exact ne_of_gt ((Real.exp_lt_one_iff).2 (by
        nlinarith [abs_pos.mpr ht]))
    have hformula :
        suzukiR1SecondKernel =ᶠ[nhds t]
          fun x => suzukiR1SecondOffOrigin |x| := by
      filter_upwards [eventually_ne_nhds ht] with x hx
      simp [suzukiR1SecondKernel, hx]
    have hcontinuous : ContinuousAt
        (fun x : Real => suzukiR1SecondOffOrigin |x|) t := by
      unfold suzukiR1SecondOffOrigin
      fun_prop (disch := simp [habs])
    exact hcontinuous.congr_of_eventuallyEq hformula

/-- Suzuki's complete smooth kernel `r'' = r₀'' + r₁''`. -/
def suzukiRSecondKernel (t : Real) : Real :=
  -(Real.exp (t / 2) + Real.exp (-t / 2)) + suzukiR1SecondKernel t

theorem continuous_suzukiRSecondKernel :
    Continuous suzukiRSecondKernel := by
  unfold suzukiRSecondKernel
  exact ((Real.continuous_exp.comp
      (continuous_id.div_const 2)).add
    (Real.continuous_exp.comp
      (continuous_id.neg.div_const 2))).neg.add
        continuous_suzukiR1SecondKernel

theorem suzukiRSecondKernel_neg (t : Real) :
    suzukiRSecondKernel (-t) = suzukiRSecondKernel t := by
  unfold suzukiRSecondKernel suzukiR1SecondKernel
  simp only [neg_div, neg_neg, abs_neg, neg_eq_zero]
  ring

@[simp]
theorem suzukiRSecondKernel_zero :
    suzukiRSecondKernel 0 = -7 / 4 := by
  simp [suzukiRSecondKernel]
  norm_num

/-- The exact `r''` kernel operator on the finite-interval `L²` space. -/
def suzukiRSecondFiniteIntervalL2Operator (a : Real) :
    SuzukiFiniteIntervalL2 a →L[Complex] SuzukiFiniteIntervalL2 a :=
  suzukiFiniteIntervalL2Operator suzukiRSecondKernel
    continuous_suzukiRSecondKernel a

theorem inner_suzukiRSecondFiniteIntervalL2Operator_continuous
    (a : Real) (u v : C(SuzukiFiniteInterval a, Complex)) :
    inner Complex
        (suzukiRSecondFiniteIntervalL2Operator a
          (suzukiFiniteIntervalContinuousToL2 a u))
        (suzukiFiniteIntervalContinuousToL2 a v) =
      conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiRSecondKernel continuous_suzukiRSecondKernel a u v) := by
  exact inner_suzukiFiniteIntervalL2Operator_continuous
    suzukiRSecondKernel continuous_suzukiRSecondKernel a u v

/-- Restriction from global `L²(Real)` to the subtype interval. The first
map changes to the restricted measure and the second pulls back along the
measure-preserving subtype inclusion. -/
def suzukiL2RestrictToFiniteInterval (a : Real) :
    SuzukiL2 →L[Complex] SuzukiFiniteIntervalL2 a :=
  (Lp.compMeasurePreservingₗᵢ Complex
      (fun x : SuzukiFiniteInterval a => (x : Real))
      (measurePreserving_subtype_coe measurableSet_Icc)).toContinuousLinearMap.comp
    (LpToLpRestrictCLM Real Complex Complex
      (volume : Measure Real) 2 (Icc (-a) a))

/-- The exact fixed-radius `r''` operator on global `L²`, obtained by
restricting to the interval and applying the adjoint restriction on output.
The adjoint is the canonical zero-extension at the Hilbert-space level. -/
def suzukiRSecondGlobalL2Operator (a : Real) :
    SuzukiL2 →L[Complex] SuzukiL2 :=
  (suzukiL2RestrictToFiniteInterval a).adjoint.comp
    ((suzukiRSecondFiniteIntervalL2Operator a).comp
      (suzukiL2RestrictToFiniteInterval a))

/-- The global operator pairing is exactly the interval operator pairing of
the two restricted `L²` vectors. -/
theorem inner_suzukiRSecondGlobalL2Operator
    (a : Real) (u v : SuzukiL2) :
    inner Complex (suzukiRSecondGlobalL2Operator a u) v =
      inner Complex
        (suzukiRSecondFiniteIntervalL2Operator a
          (suzukiL2RestrictToFiniteInterval a u))
        (suzukiL2RestrictToFiniteInterval a v) := by
  rw [suzukiRSecondGlobalL2Operator,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- The operator occurring in Suzuki's equation (2.5): the displayed double
integral is subtracted from the local form. -/
def suzukiRSecondSourceRemainderOperator (a : Real) :
    SuzukiL2 →L[Complex] SuzukiL2 :=
  -suzukiRSecondGlobalL2Operator a

/-- Suzuki's bounded finite-radius remainder with the abstract kernel
operator instantiated by the exact `r''` operator. -/
def suzukiRSecondFiniteRadiusRemainder
    {I : Type*} [DecidableEq I] (s : Finset I) (a scalar : Real)
    (coefficient shift : I → Real) (v : SuzukiL2) : Real :=
  suzukiL2FiniteRadiusRemainder s scalar coefficient shift
    (suzukiRSecondSourceRemainderOperator a) v

theorem suzukiRSecondFiniteRadiusRemainder_abs_le
    {I : Type*} [DecidableEq I] (s : Finset I) (a scalar : Real)
    (coefficient shift : I → Real) (v : SuzukiL2) :
    abs (suzukiRSecondFiniteRadiusRemainder
        s a scalar coefficient shift v) ≤
      (abs scalar +
        Finset.sum s (fun i => 2 * abs (coefficient i)) +
          norm (suzukiRSecondGlobalL2Operator a)) * norm v ^ 2 := by
  rw [← norm_neg (suzukiRSecondGlobalL2Operator a)]
  exact suzukiL2FiniteRadiusRemainder_abs_le s scalar coefficient shift
    (suzukiRSecondSourceRemainderOperator a) v

/-- The complete logarithmic radius energy with Suzuki's exact smooth-kernel
operator substituted for the formerly generic `K`. -/
def suzukiRSecondLogRadiusCompleteEnergy
    {I : Type*} [DecidableEq I] {a : Real} (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (u v : SuzukiLogRadiusCompletion a) : Complex :=
  suzukiLogRadiusCompleteEnergy s scalar coefficient shift
    (suzukiRSecondSourceRemainderOperator a) u v

theorem suzukiRSecondLogRadiusCompleteEnergy_jointContinuous
    {I : Type*} [DecidableEq I] (a : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real) :
    Continuous (Function.uncurry
      (suzukiRSecondLogRadiusCompleteEnergy (a := a)
        s scalar coefficient shift)) := by
  exact suzukiLogRadiusCompleteEnergy_jointContinuous
    a s scalar coefficient shift (suzukiRSecondSourceRemainderOperator a)

/-- Restriction of a smooth-core representative, bundled as a continuous
function on the finite interval. -/
def suzukiSmoothCoreFiniteIntervalContinuous
    {a : Real} (v : SuzukiSmoothCore a) :
    C(SuzukiFiniteInterval a, Complex) where
  toFun x := v.1 x.1
  continuous_toFun := v.1.continuous.comp continuous_subtype_val

/-- Restricting the global `L²` class of a smooth-core function gives its
literal continuous restriction to the subtype interval. -/
theorem suzukiL2RestrictToFiniteInterval_smoothCore
    {a : Real} (v : SuzukiSmoothCore a) :
    suzukiL2RestrictToFiniteInterval a (suzukiSmoothCoreToL2 v) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiSmoothCoreFiniteIntervalContinuous v) := by
  let s : Set Real := Icc (-a) a
  let restricted : Lp Complex 2 ((volume : Measure Real).restrict s) :=
    LpToLpRestrictCLM Real Complex Complex
      (volume : Measure Real) 2 s (suzukiSmoothCoreToL2 v)
  have hmp : MeasurePreserving
      (fun x : SuzukiFiniteInterval a => (x : Real))
      (volume : Measure (SuzukiFiniteInterval a))
      ((volume : Measure Real).restrict s) := by
    rw [Measure.Subtype.volume_def]
    simpa only [s] using
      (measurePreserving_subtype_coe measurableSet_Icc :
        MeasurePreserving
          (fun x : SuzukiFiniteInterval a => (x : Real))
          ((volume : Measure Real).comap Subtype.val)
          ((volume : Measure Real).restrict (Icc (-a) a)))
  have hcomp :
      Lp.compMeasurePreserving
          (fun x : SuzukiFiniteInterval a => (x : Real)) hmp restricted
        =ᵐ[volume]
      (restricted : Real → Complex) ∘
        fun x : SuzukiFiniteInterval a => (x : Real) :=
    Lp.coeFn_compMeasurePreserving restricted hmp
  have hrestrict :
      restricted =ᵐ[(volume : Measure Real).restrict s]
        suzukiSmoothCoreToL2 v := by
    simpa only [restricted] using
      (LpToLpRestrictCLM_coeFn
        (p := (2 : ENNReal)) (μ := (volume : Measure Real))
        Complex s (suzukiSmoothCoreToL2 v))
  have hrestrictComp :
      (fun x : SuzukiFiniteInterval a => restricted x.1) =ᵐ[volume]
        fun x => (suzukiSmoothCoreToL2 v) x.1 := by
    exact hmp.quasiMeasurePreserving.ae_eq_comp hrestrict
  have hsmooth :
      (suzukiSmoothCoreToL2 v : Real → Complex) =ᵐ[volume] v.1 := by
    exact (v.1.memLp (2 : ENNReal)
      (volume : Measure Real)).coeFn_toLp
  have hsmoothRestricted :
      (fun x : SuzukiFiniteInterval a =>
          (suzukiSmoothCoreToL2 v) x.1) =ᵐ[volume]
        fun x => v.1 x.1 := by
    exact hmp.quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae hsmooth)
  have hcontinuous :
      (suzukiFiniteIntervalContinuousToL2 a
          (suzukiSmoothCoreFiniteIntervalContinuous v) :
        SuzukiFiniteInterval a → Complex) =ᵐ[volume]
      (suzukiSmoothCoreFiniteIntervalContinuous v :
        SuzukiFiniteInterval a → Complex) := by
    simpa only [suzukiFiniteIntervalContinuousToL2] using
      (ContinuousMap.coeFn_toLp
        (𝕜 := Complex) (p := (2 : ENNReal))
        (volume : Measure (SuzukiFiniteInterval a))
        (suzukiSmoothCoreFiniteIntervalContinuous v))
  apply Lp.ext
  filter_upwards [hcomp, hrestrictComp, hsmoothRestricted,
    hcontinuous] with x hxComp hxRestrict hxSmooth hxContinuous
  rw [suzukiL2RestrictToFiniteInterval,
    ContinuousLinearMap.comp_apply]
  exact hxComp.trans (hxRestrict.trans (hxSmooth.trans hxContinuous.symm))

/-- On the smooth core, the global operator pairing is Suzuki's exact
polarized finite-square `r''(x-y)` double integral. -/
theorem inner_suzukiRSecondGlobalL2Operator_smoothCore
    {a : Real} (u v : SuzukiSmoothCore a) :
    inner Complex
        (suzukiRSecondGlobalL2Operator a (suzukiSmoothCoreToL2 u))
        (suzukiSmoothCoreToL2 v) =
      conj (suzukiFiniteKernelPolarizationComplex
        suzukiRSecondKernel a u.1 v.1) := by
  rw [inner_suzukiRSecondGlobalL2Operator,
    suzukiL2RestrictToFiniteInterval_smoothCore,
    suzukiL2RestrictToFiniteInterval_smoothCore,
    inner_suzukiRSecondFiniteIntervalL2Operator_continuous]
  congr 1
  change
    suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiRSecondKernel continuous_suzukiRSecondKernel a
        (suzukiFiniteIntervalRestriction a u.1 u.1.continuous)
        (suzukiFiniteIntervalRestriction a v.1 v.1.continuous) =
      suzukiFiniteKernelPolarizationComplex
        suzukiRSecondKernel a u.1 v.1
  rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
      continuous_suzukiRSecondKernel u.1.continuous v.1.continuous,
    suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
      continuous_suzukiRSecondKernel u.1.continuous v.1.continuous]

/-- Diagonally, evenness makes the exact source double integral real, so the
global Hilbert pairing equals Suzuki's displayed `r''` term without a
remaining conjugation. -/
theorem inner_suzukiRSecondGlobalL2Operator_smoothCore_self
    {a : Real} (v : SuzukiSmoothCore a) :
    inner Complex
        (suzukiRSecondGlobalL2Operator a (suzukiSmoothCoreToL2 v))
        (suzukiSmoothCoreToL2 v) =
      suzukiFiniteKernelPairingComplex suzukiRSecondKernel a v.1 := by
  rw [inner_suzukiRSecondGlobalL2Operator_smoothCore,
    suzukiFiniteKernelPolarizationComplex_self]
  have hreal :=
    suzukiFiniteKernelPolarizationComplex_conj_symm
      suzukiRSecondKernel_neg a v.1 v.1
  rw [suzukiFiniteKernelPolarizationComplex_self] at hreal
  exact hreal.symm

/-- The source remainder operator has exactly the negative diagonal pairing
appearing in equation (2.5). -/
theorem inner_suzukiRSecondSourceRemainderOperator_smoothCore_self
    {a : Real} (v : SuzukiSmoothCore a) :
    inner Complex
        (suzukiRSecondSourceRemainderOperator a (suzukiSmoothCoreToL2 v))
        (suzukiSmoothCoreToL2 v) =
      -suzukiFiniteKernelPairingComplex suzukiRSecondKernel a v.1 := by
  rw [suzukiRSecondSourceRemainderOperator,
    neg_apply, inner_neg_left,
    inner_suzukiRSecondGlobalL2Operator_smoothCore_self]

end

end M100
end Experiments
end RiemannHypothesisProject
