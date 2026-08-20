import RiemannHypothesisProject.Experiments.M100.SuzukiSourceFormDomainBridge
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# M100-DF6D2 logarithmic Fourier domain

This experimental module defines the concrete logarithmic Fourier domain
appearing in Suzuki's form-norm description. The definition is made directly
on the global `L^2` Fourier class, using the nonnegative multiplier
`sqrt (1 + posLog |xi|)`. It therefore does not depend on a pointwise
representative of the original `L^2` class.

The smooth Suzuki core maps into this domain. The proof uses Plancherel's
`L^2` Fourier transform and domination of the logarithmic multiplier by a
quadratic Schwartz multiplier. No source form identity, density theorem, or
closed-domain equality is asserted here.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- The positive logarithmic weight in Suzuki's completed form norm. -/
def suzukiLogFourierWeight (xi : Real) : Real :=
  1 + Real.posLog |xi|

theorem suzukiLogFourierWeight_one_le (xi : Real) :
    1 <= suzukiLogFourierWeight xi := by
  exact le_add_of_nonneg_right Real.posLog_nonneg

theorem suzukiLogFourierWeight_nonneg (xi : Real) :
    0 <= suzukiLogFourierWeight xi :=
  zero_le_one.trans (suzukiLogFourierWeight_one_le xi)

theorem continuous_suzukiLogFourierWeight :
    Continuous suzukiLogFourierWeight := by
  change Continuous
    ((fun _ : Real => (1 : Real)) + Function.comp Real.posLog abs)
  exact continuous_const.add
    (Real.continuous_posLog.comp continuous_abs)

/-- A quadratic pointwise majorant for the square root of the logarithmic
weight. This deliberately uses a smooth polynomial multiplier so that it
preserves Schwartz space. -/
theorem sqrt_suzukiLogFourierWeight_le_quadratic (xi : Real) :
    Real.sqrt (suzukiLogFourierWeight xi) <= 2 + xi ^ 2 := by
  have hlog : Real.posLog |xi| <= |xi| := by
    change max 0 (Real.log |xi|) <= |xi|
    exact max_le (abs_nonneg xi) (Real.log_le_self (abs_nonneg xi))
  have habs : |xi| <= 1 + xi ^ 2 := by
    nlinarith [sq_nonneg (|xi| - (1 / 2 : Real)), sq_abs xi]
  have hsqrt :
      Real.sqrt (suzukiLogFourierWeight xi) <=
        suzukiLogFourierWeight xi := by
    rw [Real.sqrt_le_left (suzukiLogFourierWeight_nonneg xi)]
    nlinarith [suzukiLogFourierWeight_one_le xi]
  exact hsqrt.trans (by
    unfold suzukiLogFourierWeight
    linarith)

/-- The logarithmically weighted Fourier representative of a global `L^2`
class. -/
def suzukiLogWeightedFourier (v : SuzukiL2) : Real -> Complex :=
  fun xi =>
    ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
      ((FourierTransform.fourier v : SuzukiL2) xi)

/-- The concrete logarithmic Fourier domain. `MemLp` is invariant under
almost-everywhere equality, so this predicate is well-defined on the `L^2`
quotient. -/
def SuzukiLogFourierDomain : Set SuzukiL2 :=
  {v | MemLp (suzukiLogWeightedFourier v) (2 : ENNReal)
    (volume : Measure Real)}

theorem suzukiLogWeightedFourier_zero_ae :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (suzukiLogWeightedFourier (0 : SuzukiL2))
      (0 : Real -> Complex) := by
  have hcoe :
      Filter.EventuallyEq (ae (volume : Measure Real))
        ((0 : SuzukiL2) : Real -> Complex) 0 :=
    Lp.coeFn_zero Complex (2 : ENNReal) (volume : Measure Real)
  filter_upwards [hcoe] with xi hxi
  unfold suzukiLogWeightedFourier
  rw [FourierTransform.fourier_zero, hxi]
  simp

theorem suzukiLogWeightedFourier_add_ae (u v : SuzukiL2) :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (suzukiLogWeightedFourier (u + v))
      (suzukiLogWeightedFourier u + suzukiLogWeightedFourier v) := by
  have hcoe := Lp.coeFn_add
    (FourierTransform.fourier u : SuzukiL2)
    (FourierTransform.fourier v : SuzukiL2)
  filter_upwards [hcoe] with xi hxi
  unfold suzukiLogWeightedFourier
  rw [FourierTransform.fourier_add, hxi]
  simp only [Pi.add_apply, mul_add]

theorem suzukiLogWeightedFourier_smul_ae (c : Complex) (v : SuzukiL2) :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (suzukiLogWeightedFourier (c • v))
      (c • suzukiLogWeightedFourier v) := by
  have hcoe := Lp.coeFn_smul c
    (FourierTransform.fourier v : SuzukiL2)
  filter_upwards [hcoe] with xi hxi
  have hxi' :
      (((c • (FourierTransform.fourier v : SuzukiL2) :
        SuzukiL2)) xi) =
        c * ((FourierTransform.fourier v : SuzukiL2) xi) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hxi
  unfold suzukiLogWeightedFourier
  rw [FourierTransform.fourier_smul, hxi']
  change
    ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
        (c * ((FourierTransform.fourier v : SuzukiL2) xi)) =
      c * (((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
        ((FourierTransform.fourier v : SuzukiL2) xi))
  ring

theorem suzukiLogFourierDomain_zero :
    SuzukiLogFourierDomain (0 : SuzukiL2) := by
  exact MemLp.zero.ae_eq suzukiLogWeightedFourier_zero_ae.symm

theorem suzukiLogFourierDomain_add {u v : SuzukiL2}
    (hu : SuzukiLogFourierDomain u)
    (hv : SuzukiLogFourierDomain v) :
    SuzukiLogFourierDomain (u + v) := by
  exact (hu.add hv).ae_eq (suzukiLogWeightedFourier_add_ae u v).symm

theorem suzukiLogFourierDomain_smul (c : Complex) {v : SuzukiL2}
    (hv : SuzukiLogFourierDomain v) :
    SuzukiLogFourierDomain (c • v) := by
  exact (hv.const_smul c).ae_eq
    (suzukiLogWeightedFourier_smul_ae c v).symm

/-- The concrete logarithmic Fourier domain bundled as a complex submodule of
the ambient global `L^2` space. -/
def SuzukiLogFourierSubmodule : Submodule Complex SuzukiL2 where
  carrier := SuzukiLogFourierDomain
  zero_mem' := suzukiLogFourierDomain_zero
  add_mem' := suzukiLogFourierDomain_add
  smul_mem' := suzukiLogFourierDomain_smul

/-- The logarithmic multiplier applied to a Schwartz function is in `L^2`.
The proof avoids differentiating the nonsmooth logarithmic weight: it is
dominated pointwise by the smooth multiplier `2 + xi^2`. -/
theorem schwartz_memLp_suzukiLogWeighted
    (f : SchwartzLineTestFunction) :
    MemLp
      (fun xi : Real =>
        ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) * f xi)
      (2 : ENNReal) (volume : Measure Real) := by
  let quadraticMultiplier : SchwartzLineTestFunction :=
    SchwartzMap.smulLeftCLM Complex (fun xi : Real => 2 + xi ^ 2) f
  have hgrowth :
      Function.HasTemperateGrowth (fun xi : Real => (2 : Real) + xi ^ 2) := by
    fun_prop
  have hquadratic :
      MemLp (quadraticMultiplier : Real -> Complex)
        (2 : ENNReal) (volume : Measure Real) :=
    quadraticMultiplier.memLp
      (2 : ENNReal) (volume : Measure Real)
  apply hquadratic.mono
  next =>
    have hcontinuous : Continuous
        (fun xi : Real =>
          ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
            f xi) := by
      exact (Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp
          continuous_suzukiLogFourierWeight)).mul f.continuous
    exact hcontinuous.aestronglyMeasurable
  next =>
    filter_upwards with xi
    rw [show quadraticMultiplier xi =
        (((2 + xi ^ 2 : Real) : Complex) * (f xi)) by
      simpa only [quadraticMultiplier, Complex.real_smul] using
        SchwartzMap.smulLeftCLM_apply_apply hgrowth f xi]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by positivity : 0 <= (2 + xi ^ 2 : Real))]
    exact mul_le_mul_of_nonneg_right
      (sqrt_suzukiLogFourierWeight_le_quadratic xi)
      (norm_nonneg (f xi))

/-- Every Suzuki smooth-core function belongs to the concrete logarithmic
Fourier domain after passage to the global `L^2` quotient. -/
theorem suzukiSmoothCoreToL2_mem_logFourierDomain
    {r : Real} (v : SuzukiSmoothCore r) :
    SuzukiLogFourierDomain (suzukiSmoothCoreToL2 v) := by
  have hschwartz := schwartz_memLp_suzukiLogWeighted
    (SchwartzMap.fourierTransformCLM Complex v.1)
  have hsmoothToLp :
      suzukiSmoothCoreToL2 v =
        v.1.toLp (2 : ENNReal) (volume : Measure Real) := by
    apply Lp.ext
    filter_upwards [
      (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp,
      SchwartzMap.coeFn_toLp v.1 (2 : ENNReal)
        (volume : Measure Real)] with xi hleft hright
    exact hleft.trans hright.symm
  have hfourier :
      FourierTransform.fourier (suzukiSmoothCoreToL2 v) =
        (SchwartzMap.fourierTransformCLM Complex v.1).toLp
          (2 : ENNReal) (volume : Measure Real) := by
    rw [hsmoothToLp]
    simpa only [SchwartzMap.fourierTransformCLM_apply] using
      (SchwartzMap.toLp_fourier_eq v.1)
  have hfourierCoe :
      Filter.EventuallyEq (ae (volume : Measure Real))
        (SchwartzMap.fourierTransformCLM Complex v.1)
        (fun xi : Real =>
          ((FourierTransform.fourier (suzukiSmoothCoreToL2 v) :
            SuzukiL2) xi)) := by
    rw [hfourier]
    exact (((SchwartzMap.fourierTransformCLM Complex v.1).memLp
      (2 : ENNReal) (volume : Measure Real)).coeFn_toLp).symm
  unfold SuzukiLogFourierDomain suzukiLogWeightedFourier
  apply hschwartz.ae_eq
  filter_upwards [hfourierCoe] with xi hxi
  rw [hxi]

end

end M100
end Experiments
end RiemannHypothesisProject
