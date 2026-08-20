import RiemannHypothesisProject.Experiments.M100.SuzukiFiniteRemainderBound
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder

/-!
# M100-DF6D2 closed logarithmic Fourier multiplier

This module bundles the logarithmically weighted Fourier transform as a
partially defined linear operator on global `L^2`. Its domain is exactly
`SuzukiLogFourierSubmodule`. The graph topology is the concrete shifted local
form topology suggested by Suzuki's Fourier description.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- The `L^2` class of the logarithmically weighted Fourier representative. -/
def suzukiLogWeightedFourierToL2
    (v : SuzukiLogFourierSubmodule) : SuzukiL2 :=
  v.2.toLp (suzukiLogWeightedFourier v.1)

theorem suzukiLogWeightedFourierToL2_coe_ae
    (v : SuzukiLogFourierSubmodule) :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (suzukiLogWeightedFourierToL2 v : Real → Complex)
      (suzukiLogWeightedFourier v.1) :=
  v.2.coeFn_toLp

/-- The bounded reciprocal of the square-root logarithmic weight. -/
def suzukiLogFourierInvMultiplier (xi : Real) : Complex :=
  (((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex))⁻¹

theorem suzukiLogFourierInvMultiplier_norm_le_one (xi : Real) :
    ‖suzukiLogFourierInvMultiplier xi‖ ≤ 1 := by
  have hroot : 1 ≤ Real.sqrt (suzukiLogFourierWeight xi) := by
    exact Real.one_le_sqrt.mpr (suzukiLogFourierWeight_one_le xi)
  simp only [suzukiLogFourierInvMultiplier, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_le_one_of_one_le₀ hroot

theorem continuous_suzukiLogFourierInvMultiplier :
    Continuous suzukiLogFourierInvMultiplier := by
  apply Continuous.inv₀
  · exact Complex.continuous_ofReal.comp
      continuous_suzukiLogFourierWeight.sqrt
  · intro xi
    exact Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.mpr
        (lt_of_lt_of_le zero_lt_one
          (suzukiLogFourierWeight_one_le xi)))

/-- The reciprocal weight as an essentially bounded multiplier. -/
def suzukiLogFourierInvMultiplierLInfinity :
    Lp Complex ∞ (volume : Measure Real) :=
  (memLp_top_of_bound
    continuous_suzukiLogFourierInvMultiplier.aestronglyMeasurable
    1 (Filter.Eventually.of_forall
      suzukiLogFourierInvMultiplier_norm_le_one)).toLp
    suzukiLogFourierInvMultiplier

theorem suzukiLogFourierInvMultiplierLInfinity_coe_ae :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (suzukiLogFourierInvMultiplierLInfinity : Real → Complex)
      suzukiLogFourierInvMultiplier := by
  exact MemLp.coeFn_toLp _

/-- Multiplication by the reciprocal weight as a linear map on global `L²`. -/
def suzukiLogFourierInvMultiplierLinearMap : SuzukiL2 →ₗ[Complex] SuzukiL2 where
  toFun := fun v ↦ suzukiLogFourierInvMultiplierLInfinity • v
  map_add' := by
    intro u v
    exact Lp.add_smul suzukiLogFourierInvMultiplierLInfinity u v
  map_smul' := by
    intro c v
    change suzukiLogFourierInvMultiplierLInfinity • (c • v) =
      c • (suzukiLogFourierInvMultiplierLInfinity • v)
    simpa only [smul_smul] using
      (Lp.smul_comm c suzukiLogFourierInvMultiplierLInfinity v).symm

/-- Multiplication by the reciprocal weight is bounded on global `L²`. -/
def suzukiLogFourierInvMultiplierCLM : SuzukiL2 →L[Complex] SuzukiL2 :=
  LinearMap.mkContinuous suzukiLogFourierInvMultiplierLinearMap
    ‖suzukiLogFourierInvMultiplierLInfinity‖
    (Lp.norm_smul_le suzukiLogFourierInvMultiplierLInfinity)

theorem suzukiLogFourierInvMultiplierCLM_coe_ae (v : SuzukiL2) :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (suzukiLogFourierInvMultiplierCLM v : Real → Complex)
      (fun xi ↦ suzukiLogFourierInvMultiplier xi * v xi) := by
  have hholder :
      Filter.EventuallyEq (ae (volume : Measure Real))
        ((suzukiLogFourierInvMultiplierLInfinity • v : SuzukiL2) :
          Real → Complex)
        ((suzukiLogFourierInvMultiplierLInfinity : Real → Complex) •
          (v : Real → Complex)) :=
    Lp.coeFn_lpSMul (p := (∞ : ENNReal)) (q := (2 : ENNReal))
      (r := (2 : ENNReal)) suzukiLogFourierInvMultiplierLInfinity v
  filter_upwards [
    hholder,
    suzukiLogFourierInvMultiplierLInfinity_coe_ae] with xi hholder hinv
  simpa [suzukiLogFourierInvMultiplierCLM,
    suzukiLogFourierInvMultiplierLinearMap, hinv] using hholder

theorem suzukiLogFourierInvMultiplier_mul_weighted (v : SuzukiL2) (xi : Real) :
    suzukiLogFourierInvMultiplier xi * suzukiLogWeightedFourier v xi =
      (FourierTransform.fourier v : SuzukiL2) xi := by
  have hroot : Real.sqrt (suzukiLogFourierWeight xi) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr
      (lt_of_lt_of_le zero_lt_one (suzukiLogFourierWeight_one_le xi))
  have hrootComplex :
      ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hroot
  unfold suzukiLogFourierInvMultiplier suzukiLogWeightedFourier
  rw [← mul_assoc, inv_mul_cancel₀ hrootComplex, one_mul]

theorem suzukiLogFourierInvMultiplierCLM_weightedToL2
    (v : SuzukiLogFourierSubmodule) :
    suzukiLogFourierInvMultiplierCLM
      (suzukiLogWeightedFourierToL2 v) =
        FourierTransform.fourier v.1 := by
  apply Lp.ext
  filter_upwards [
    suzukiLogFourierInvMultiplierCLM_coe_ae
      (suzukiLogWeightedFourierToL2 v),
    suzukiLogWeightedFourierToL2_coe_ae v] with xi hinv hweighted
  rw [hinv, hweighted,
    suzukiLogFourierInvMultiplier_mul_weighted v.1 xi]

theorem suzukiLogWeightedFourier_eq_of_fourier_eq_invMultiplier
    {v y : SuzukiL2}
    (h : FourierTransform.fourier v =
      suzukiLogFourierInvMultiplierCLM y) :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (suzukiLogWeightedFourier v) (y : Real → Complex) := by
  have hFourier :
      Filter.EventuallyEq (ae (volume : Measure Real))
        ((FourierTransform.fourier v : SuzukiL2) : Real → Complex)
        (suzukiLogFourierInvMultiplierCLM y : Real → Complex) := by
    rw [h]
  filter_upwards [hFourier,
    suzukiLogFourierInvMultiplierCLM_coe_ae y] with xi hFourier hinv
  have hroot : Real.sqrt (suzukiLogFourierWeight xi) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr
      (lt_of_lt_of_le zero_lt_one (suzukiLogFourierWeight_one_le xi))
  have hrootComplex :
      ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hroot
  unfold suzukiLogWeightedFourier
  rw [hFourier, hinv]
  change
    ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
      (((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex)⁻¹ * y xi) =
        y xi
  rw [← mul_assoc, mul_inv_cancel₀ hrootComplex, one_mul]

theorem suzukiLogFourier_mem_domain_of_fourier_eq_invMultiplier
    {v y : SuzukiL2}
    (h : FourierTransform.fourier v =
      suzukiLogFourierInvMultiplierCLM y) :
    v ∈ SuzukiLogFourierSubmodule := by
  exact (memLp_congr_ae
    (suzukiLogWeightedFourier_eq_of_fourier_eq_invMultiplier h)).mpr
      (Lp.memLp y)

theorem suzukiLogWeightedFourierToL2_eq_of_fourier_eq_invMultiplier
    {v y : SuzukiL2}
    (h : FourierTransform.fourier v =
      suzukiLogFourierInvMultiplierCLM y) :
    suzukiLogWeightedFourierToL2
      ⟨v, suzukiLogFourier_mem_domain_of_fourier_eq_invMultiplier h⟩ = y := by
  apply Lp.ext
  filter_upwards [
    suzukiLogWeightedFourierToL2_coe_ae
      ⟨v, suzukiLogFourier_mem_domain_of_fourier_eq_invMultiplier h⟩,
    suzukiLogWeightedFourier_eq_of_fourier_eq_invMultiplier h] with
      xi htoLp hweighted
  exact htoLp.trans hweighted

/-- Linearity of the weighted Fourier multiplier on its maximal `L^2`
domain. -/
def suzukiLogWeightedFourierLinearMap :
    SuzukiLogFourierSubmodule →ₗ[Complex] SuzukiL2 where
  toFun := suzukiLogWeightedFourierToL2
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [
      suzukiLogWeightedFourierToL2_coe_ae (u + v),
      suzukiLogWeightedFourierToL2_coe_ae u,
      suzukiLogWeightedFourierToL2_coe_ae v,
      Lp.coeFn_add (suzukiLogWeightedFourierToL2 u)
        (suzukiLogWeightedFourierToL2 v),
      suzukiLogWeightedFourier_add_ae u.1 v.1] with
        xi hsum hu hv hadd hweight
    calc
      (suzukiLogWeightedFourierToL2 (u + v) : Real → Complex) xi =
          suzukiLogWeightedFourier (u.1 + v.1) xi := hsum
      _ = suzukiLogWeightedFourier u.1 xi +
          suzukiLogWeightedFourier v.1 xi := hweight
      _ = (suzukiLogWeightedFourierToL2 u : Real → Complex) xi +
          (suzukiLogWeightedFourierToL2 v : Real → Complex) xi := by
        rw [hu, hv]
      _ = ((suzukiLogWeightedFourierToL2 u +
          suzukiLogWeightedFourierToL2 v : SuzukiL2) :
            Real → Complex) xi := hadd.symm
  map_smul' := by
    intro c v
    apply Lp.ext
    filter_upwards [
      suzukiLogWeightedFourierToL2_coe_ae (c • v),
      suzukiLogWeightedFourierToL2_coe_ae v,
      Lp.coeFn_smul c (suzukiLogWeightedFourierToL2 v),
      suzukiLogWeightedFourier_smul_ae c v.1] with
        xi hleft hv hsmul hweight
    calc
      (suzukiLogWeightedFourierToL2 (c • v) : Real → Complex) xi =
          suzukiLogWeightedFourier (c • v.1) xi := hleft
      _ = (c • suzukiLogWeightedFourier v.1) xi := hweight
      _ = c * suzukiLogWeightedFourier v.1 xi := by
        simp only [Pi.smul_apply, smul_eq_mul]
      _ = c * (suzukiLogWeightedFourierToL2 v : Real → Complex) xi := by
        rw [hv]
      _ = ((c • suzukiLogWeightedFourierToL2 v : SuzukiL2) :
          Real → Complex) xi := hsmul.symm

/-- The logarithmic Fourier multiplier as an unbounded operator on global
`L^2`, with its maximal weighted domain. -/
def suzukiLogFourierPMap :
    LinearPMap (RingHom.id Complex) SuzukiL2 SuzukiL2 where
  domain := SuzukiLogFourierSubmodule
  toFun := suzukiLogWeightedFourierLinearMap

@[simp]
theorem suzukiLogFourierPMap_domain :
    suzukiLogFourierPMap.domain = SuzukiLogFourierSubmodule :=
  rfl

@[simp]
theorem suzukiLogFourierPMap_apply
    (v : SuzukiLogFourierSubmodule) :
    suzukiLogFourierPMap v = suzukiLogWeightedFourierToL2 v :=
  rfl

theorem suzukiLogFourierPMap_mem_graph_iff (x : SuzukiL2 × SuzukiL2) :
    x ∈ suzukiLogFourierPMap.graph ↔
      FourierTransform.fourier x.1 =
        suzukiLogFourierInvMultiplierCLM x.2 := by
  constructor
  · rw [LinearPMap.mem_graph_iff]
    rintro ⟨v, hv, hy⟩
    change suzukiLogWeightedFourierToL2 ⟨v.1, v.2⟩ = x.2 at hy
    calc
      FourierTransform.fourier x.1 =
          FourierTransform.fourier v.1 := by rw [hv]
      _ = suzukiLogFourierInvMultiplierCLM
          (suzukiLogWeightedFourierToL2 ⟨v.1, v.2⟩) :=
        (suzukiLogFourierInvMultiplierCLM_weightedToL2
          ⟨v.1, v.2⟩).symm
      _ = suzukiLogFourierInvMultiplierCLM x.2 := by rw [hy]
  · intro h
    rw [LinearPMap.mem_graph_iff]
    let hv : SuzukiLogFourierSubmodule :=
      ⟨x.1, suzukiLogFourier_mem_domain_of_fourier_eq_invMultiplier h⟩
    refine ⟨hv, rfl, ?_⟩
    exact suzukiLogWeightedFourierToL2_eq_of_fourier_eq_invMultiplier h

/-- The maximal logarithmic Fourier multiplier is a closed unbounded
operator. -/
theorem suzukiLogFourierPMap_isClosed :
    suzukiLogFourierPMap.IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph :
      (suzukiLogFourierPMap.graph : Set (SuzukiL2 × SuzukiL2)) =
        {x | FourierTransform.fourier x.1 =
          suzukiLogFourierInvMultiplierCLM x.2} := by
    ext x
    exact suzukiLogFourierPMap_mem_graph_iff x
  rw [hgraph]
  exact isClosed_eq
    ((MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous.comp
      continuous_fst)
    (suzukiLogFourierInvMultiplierCLM.continuous.comp continuous_snd)

/-- The concrete completed local form domain, realized as the closed graph
of the logarithmic Fourier multiplier in global `L² × L²`. -/
def SuzukiLogGraphSpace := suzukiLogFourierPMap.graph

noncomputable instance : CompleteSpace SuzukiLogGraphSpace :=
  suzukiLogFourierPMap_isClosed.completeSpace_coe

end

end M100
end Experiments
end RiemannHypothesisProject
