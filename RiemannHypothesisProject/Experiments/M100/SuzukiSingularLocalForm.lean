import RiemannHypothesisProject.Experiments.M100.SuzukiLogRadiusCompletion
import RiemannHypothesisProject.Experiments.M100.SuzukiRSecondKernel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# M100-DF6D2 Suzuki singular local form

This experimental module fixes the exact Lean expressions corresponding to
Suzuki's equations (2.3) and (2.6).  The physical-side expression is the
singular difference form on `(-a,a)` with its logarithmic boundary potential.
The Fourier-side expression uses Mathlib's unitary convention
`exp (-2 * pi * I * x * xi)`, so the paper's variable change `z = -2*pi*xi`
absorbs the displayed `1/(2*pi)` and changes the multiplier to
`log (2*pi*|xi|) + EulerGamma`.

The value assigned to either logarithmic or diagonal singularity is immaterial
to the integral, but is kept explicit through Lean's totalized `log`, inverse,
and division operations.  This file does not postulate the source identity:
the exact theorem target is named below and remains a theorem to prove.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate Interval

/-- Polarized difference quotient in the first term of Suzuki (2.3). -/
def suzukiSingularDifferencePolarization
    (u v : Real → Complex) (x y : Real) : Complex :=
  (((|x - y|⁻¹ : Real) : Complex) *
    ((u x - u y) * conj (v x - v y)))

/-- Polarized logarithmic boundary integrand in Suzuki (2.3). -/
def suzukiSingularBoundaryPolarization
    (a : Real) (u v : Real → Complex) (x : Real) : Complex :=
  ((Real.log (a ^ 2 - x ^ 2) : Real) : Complex) *
    (u x * conj (v x))

/-- The exact complex-polarized singular local form from Suzuki (2.3). -/
def suzukiSingularLocalPolarizedForm
    (a : Real) (u v : Real → Complex) : Complex :=
  (1 / 4 : Complex) *
      (∫ p in suzukiFiniteSquare a,
        suzukiSingularDifferencePolarization u v p.1 p.2) -
    (1 / 2 : Complex) *
      (∫ x in Icc (-a) a,
        suzukiSingularBoundaryPolarization a u v x)

/-- The real diagonal singular local expression displayed in Suzuki (2.3). -/
def suzukiSingularLocalForm
    (a : Real) (v : Real → Complex) : Real :=
  (1 / 4 : Real) *
      (∫ p in suzukiFiniteSquare a,
        ‖v p.1 - v p.2‖ ^ 2 / |p.1 - p.2|) -
    (1 / 2 : Real) *
      (∫ x in Icc (-a) a,
        Real.log (a ^ 2 - x ^ 2) * ‖v x‖ ^ 2)

/-- On the diagonal, the polarized difference integrand is exactly the real
norm-square quotient in (2.3). -/
theorem suzukiSingularDifferencePolarization_self_re
    (v : Real → Complex) (x y : Real) :
    (suzukiSingularDifferencePolarization v v x y).re =
      ‖v x - v y‖ ^ 2 / |x - y| := by
  rw [suzukiSingularDifferencePolarization, Complex.mul_conj']
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  norm_cast
  rw [inv_mul_eq_div]

/-- On the diagonal, the polarized boundary integrand is exactly the real
boundary term in (2.3). -/
theorem suzukiSingularBoundaryPolarization_self_re
    (a : Real) (v : Real → Complex) (x : Real) :
    (suzukiSingularBoundaryPolarization a v v x).re =
      Real.log (a ^ 2 - x ^ 2) * ‖v x‖ ^ 2 := by
  rw [suzukiSingularBoundaryPolarization, Complex.mul_conj']
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  norm_cast

/-- A Schwartz function is globally Lipschitz, with the concrete constant
given by the bounded-continuous norm of its Schwartz derivative. -/
theorem schwartz_lipschitzWith_derivBound
    (v : SchwartzLineTestFunction) :
    LipschitzWith
      ‖(SchwartzMap.derivCLM Complex Complex v).toBoundedContinuousFunction‖₊
      v := by
  have hv : Differentiable Real (v : Real → Complex) := v.differentiable
  apply lipschitzWith_of_nnnorm_deriv_le (𝕜 := Real) hv
  intro x
  change ‖SchwartzMap.derivCLM Complex Complex v x‖₊ ≤ _
  exact_mod_cast
    (SchwartzMap.derivCLM Complex Complex v).toBoundedContinuousFunction
      |>.norm_coe_le_norm x

/-- The diagonal singularity is removable at the level of the polarized
difference integrand: its norm is bounded by a constant times `|x-y|`. -/
theorem norm_suzukiSingularDifferencePolarization_le
    (u v : SchwartzLineTestFunction) (x y : Real) :
    ‖suzukiSingularDifferencePolarization u v x y‖ ≤
      (‖(SchwartzMap.derivCLM Complex Complex u).toBoundedContinuousFunction‖ *
        ‖(SchwartzMap.derivCLM Complex Complex v).toBoundedContinuousFunction‖) *
        |x - y| := by
  let Cu : Real :=
    ‖(SchwartzMap.derivCLM Complex Complex u).toBoundedContinuousFunction‖
  let Cv : Real :=
    ‖(SchwartzMap.derivCLM Complex Complex v).toBoundedContinuousFunction‖
  have hu : ‖u x - u y‖ ≤ Cu * |x - y| := by
    simpa only [dist_eq_norm, Real.dist_eq, Cu, NNReal.smul_def,
      coe_nnnorm, Real.norm_eq_abs] using
      (schwartz_lipschitzWith_derivBound u).dist_le_mul x y
  have hv : ‖v x - v y‖ ≤ Cv * |x - y| := by
    simpa only [dist_eq_norm, Real.dist_eq, Cv, NNReal.smul_def,
      coe_nnnorm, Real.norm_eq_abs] using
      (schwartz_lipschitzWith_derivBound v).dist_le_mul x y
  by_cases hxy : x = y
  · subst y
    simp [suzukiSingularDifferencePolarization]
  · have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hmul :
        ‖u x - u y‖ * ‖v x - v y‖ ≤
          (Cu * Cv) * |x - y| ^ 2 := by
      calc
        ‖u x - u y‖ * ‖v x - v y‖ ≤
            (Cu * |x - y|) * (Cv * |x - y|) :=
          mul_le_mul hu hv (norm_nonneg _) (by positivity)
        _ = (Cu * Cv) * |x - y| ^ 2 := by ring
    rw [suzukiSingularDifferencePolarization, norm_mul, norm_mul,
      Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_abs, inv_mul_eq_div]
    change
      ‖u x - u y‖ * ‖v x - v y‖ / |x - y| ≤
        (Cu * Cv) * |x - y|
    exact (div_le_iff₀ hd).2 (by
      simpa only [pow_two, mul_assoc] using hmul)

/-- The polarized singular difference term is integrable on every finite
Suzuki square. -/
theorem integrableOn_suzukiSingularDifferencePolarization
    (a : Real) (u v : SchwartzLineTestFunction) :
    IntegrableOn
      (fun p : Real × Real =>
        suzukiSingularDifferencePolarization u v p.1 p.2)
      (suzukiFiniteSquare a) := by
  have hmeas : Measurable
      (fun p : Real × Real =>
        suzukiSingularDifferencePolarization u v p.1 p.2) := by
    unfold suzukiSingularDifferencePolarization
    fun_prop
  apply Measure.integrableOn_of_bounded
    (isCompact_suzukiFiniteSquare a).measure_ne_top
    hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (isCompact_suzukiFiniteSquare a).measurableSet] with p hp
  have habs : |p.1 - p.2| ≤ 2 * |a| := by
    rcases hp with ⟨⟨hp1l, hp1r⟩, ⟨hp2l, hp2r⟩⟩
    have hraw : |p.1 - p.2| ≤ 2 * a := by
      rw [abs_le]
      constructor <;> linarith
    exact hraw.trans (mul_le_mul_of_nonneg_left (le_abs_self a) (by positivity))
  exact (norm_suzukiSingularDifferencePolarization_le u v p.1 p.2).trans
    (mul_le_mul_of_nonneg_left habs (by positivity))

/-- The logarithmic boundary coefficient in (2.3) is interval-integrable,
including its two endpoint singularities. -/
theorem intervalIntegrable_suzukiSingularBoundaryLog (a : Real) :
    IntervalIntegrable
      (fun x : Real => Real.log (a ^ 2 - x ^ 2)) volume (-a) a := by
  have hanalytic : AnalyticOnNhd Real
      (fun x : Real => a ^ 2 - x ^ 2) [[-a, a]] := by
    exact analyticOnNhd_const.sub (analyticOnNhd_id.pow 2)
  exact hanalytic.meromorphicOn.intervalIntegrable_log

/-- The polarized logarithmic boundary term is integrable on the finite
interval for every nonnegative radius. -/
theorem integrableOn_suzukiSingularBoundaryPolarization
    {a : Real} (ha : 0 ≤ a) (u v : SchwartzLineTestFunction) :
    IntegrableOn (suzukiSingularBoundaryPolarization a u v)
      (Icc (-a) a) := by
  have hcontinuous : ContinuousOn
      (fun x : Real => u x * conj (v x)) [[-a, a]] := by
    fun_prop
  have hint : IntervalIntegrable
      (suzukiSingularBoundaryPolarization a u v) volume (-a) a := by
    have hsmul :=
      (intervalIntegrable_suzukiSingularBoundaryLog a).smul_continuousOn
        hcontinuous
    change IntervalIntegrable
      (fun x : Real =>
        ((Real.log (a ^ 2 - x ^ 2) : Real) : Complex) *
          (u x * conj (v x))) volume (-a) a
    simpa only [Complex.real_smul] using hsmul
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 hint

/-- The real part of the diagonal polarized form is exactly Suzuki's real
singular local expression (2.3). -/
theorem suzukiSingularLocalPolarizedForm_self_re
    {a : Real} (ha : 0 ≤ a) (v : SuzukiSmoothCore a) :
    (suzukiSingularLocalPolarizedForm a v.1 v.1).re =
      suzukiSingularLocalForm a v.1 := by
  have hdiffInt :=
    integrableOn_suzukiSingularDifferencePolarization a v.1 v.1
  have hboundaryInt :=
    integrableOn_suzukiSingularBoundaryPolarization ha v.1 v.1
  have hdiffRe :
      (∫ p in suzukiFiniteSquare a,
          suzukiSingularDifferencePolarization v.1 v.1 p.1 p.2).re =
        ∫ p in suzukiFiniteSquare a,
          ‖v.1 p.1 - v.1 p.2‖ ^ 2 / |p.1 - p.2| := by
    calc
      (∫ p in suzukiFiniteSquare a,
          suzukiSingularDifferencePolarization v.1 v.1 p.1 p.2).re =
          ∫ p in suzukiFiniteSquare a,
            (suzukiSingularDifferencePolarization
              v.1 v.1 p.1 p.2).re :=
        (integral_re hdiffInt).symm
      _ = ∫ p in suzukiFiniteSquare a,
          ‖v.1 p.1 - v.1 p.2‖ ^ 2 / |p.1 - p.2| := by
        apply integral_congr_ae
        filter_upwards with p
        exact suzukiSingularDifferencePolarization_self_re v.1 p.1 p.2
  have hboundaryRe :
      (∫ x in Icc (-a) a,
          suzukiSingularBoundaryPolarization a v.1 v.1 x).re =
        ∫ x in Icc (-a) a,
          Real.log (a ^ 2 - x ^ 2) * ‖v.1 x‖ ^ 2 := by
    calc
      (∫ x in Icc (-a) a,
          suzukiSingularBoundaryPolarization a v.1 v.1 x).re =
          ∫ x in Icc (-a) a,
            (suzukiSingularBoundaryPolarization a v.1 v.1 x).re :=
        (integral_re hboundaryInt).symm
      _ = ∫ x in Icc (-a) a,
          Real.log (a ^ 2 - x ^ 2) * ‖v.1 x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        exact suzukiSingularBoundaryPolarization_self_re a v.1 x
  unfold suzukiSingularLocalPolarizedForm suzukiSingularLocalForm
  rw [Complex.sub_re, Complex.mul_re, Complex.mul_re]
  norm_num [Complex.div_re, Complex.div_im]
  rw [hdiffRe, hboundaryRe]

/-- The Fourier multiplier obtained from Suzuki (2.6) after conversion to
Mathlib's Fourier normalization. -/
def suzukiSourceLogFourierWeight (xi : Real) : Real :=
  Real.log (2 * Real.pi * |xi|) + Real.eulerMascheroniConstant

/-- The exact complex-polarized Fourier expression corresponding to Suzuki
(2.6) in Mathlib's normalization. -/
def suzukiSourceLogFourierPolarizedForm
    (u v : SchwartzLineTestFunction) : Complex :=
  ∫ xi : Real,
    ((suzukiSourceLogFourierWeight xi : Real) : Complex) *
      (SchwartzMap.fourierTransformCLM Complex u xi *
        conj (SchwartzMap.fourierTransformCLM Complex v xi))

/-- The real diagonal Fourier expression corresponding to Suzuki (2.6) in
Mathlib's normalization. -/
def suzukiSourceLogFourierForm
    (v : SchwartzLineTestFunction) : Real :=
  ∫ xi : Real,
    suzukiSourceLogFourierWeight xi *
      ‖SchwartzMap.fourierTransformCLM Complex v xi‖ ^ 2

/-- Away from the null frequency, the converted source multiplier separates
into the Mathlib-frequency logarithm and the fixed normalization constant. -/
theorem suzukiSourceLogFourierWeight_eq
    {xi : Real} (hxi : xi ≠ 0) :
    suzukiSourceLogFourierWeight xi =
      Real.log |xi| +
        (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant) := by
  have hscale : (2 * Real.pi : Real) ≠ 0 := by positivity
  have habs : |xi| ≠ 0 := abs_ne_zero.mpr hxi
  unfold suzukiSourceLogFourierWeight
  rw [Real.log_mul hscale habs]
  ring

/-- The converted logarithmic multiplier is integrable across its removable
point-value singularity at frequency zero on `[-1,1]`. -/
theorem intervalIntegrable_suzukiSourceLogFourierWeight :
    IntervalIntegrable suzukiSourceLogFourierWeight volume (-1) 1 := by
  have hscale : 0 < (2 * Real.pi : Real) := by positivity
  have hanalytic : AnalyticOnNhd Real
      (fun xi : Real => (2 * Real.pi) * xi) [[(-1 : Real), 1]] := by
    exact analyticOnNhd_const.mul analyticOnNhd_id
  have hlog : IntervalIntegrable
      (fun xi : Real => Real.log ((2 * Real.pi) * xi))
      volume (-1) 1 :=
    hanalytic.meromorphicOn.intervalIntegrable_log
  have hsum : IntervalIntegrable
      (fun xi : Real =>
        Real.log ((2 * Real.pi) * xi) + Real.eulerMascheroniConstant)
      volume (-1) 1 :=
    hlog.add intervalIntegrable_const
  apply hsum.congr
  intro xi _hxi
  unfold suzukiSourceLogFourierWeight
  rw [show Real.log (2 * Real.pi * |xi|) =
      Real.log ((2 * Real.pi) * xi) by
    calc
      Real.log (2 * Real.pi * |xi|) =
          Real.log |(2 * Real.pi) * xi| := by
        rw [abs_mul, abs_of_pos hscale]
      _ = Real.log ((2 * Real.pi) * xi) := Real.log_abs _]

/-- Outside the unit frequency interval, the exact source multiplier is
dominated by a fixed multiple of the positive logarithmic graph weight. -/
theorem abs_suzukiSourceLogFourierWeight_le
    {xi : Real} (hxi : 1 ≤ |xi|) :
    abs (suzukiSourceLogFourierWeight xi) ≤
      (abs (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant) + 1) *
        suzukiLogFourierWeight xi := by
  have habsPos : 0 < |xi| := lt_of_lt_of_le zero_lt_one hxi
  have hxi0 : xi ≠ 0 := abs_pos.mp habsPos
  have hlogNonneg : 0 ≤ Real.log |xi| := Real.log_nonneg hxi
  have hposLog : Real.posLog |xi| = Real.log |xi| := by
    have hxi' : 1 ≤ abs (abs xi) := by simpa only [abs_abs] using hxi
    exact Real.posLog_eq_log hxi'
  rw [suzukiSourceLogFourierWeight_eq hxi0]
  have habs := abs_add_le (Real.log |xi|)
    (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant)
  unfold suzukiLogFourierWeight
  rw [hposLog]
  calc
    abs (Real.log |xi| +
        (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant)) ≤
        abs (Real.log |xi|) +
          abs (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant) := habs
    _ = Real.log |xi| +
          abs (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant) := by
      rw [abs_of_nonneg hlogNonneg]
    _ ≤ (abs (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant) + 1) *
          (1 + Real.log |xi|) := by
      nlinarith [mul_nonneg
        (abs_nonneg (Real.log (2 * Real.pi) +
          Real.eulerMascheroniConstant)) hlogNonneg]

/-- The exact Fourier-side diagonal integrand in (2.6) is genuinely
integrable for every Schwartz function; the Bochner integral therefore does
not fall back to its nonintegrable default value. -/
theorem integrable_suzukiSourceLogFourierFormIntegrand
    (v : SchwartzLineTestFunction) :
    Integrable
      (fun xi : Real =>
        suzukiSourceLogFourierWeight xi *
          ‖SchwartzMap.fourierTransformCLM Complex v xi‖ ^ 2) := by
  let f : SchwartzLineTestFunction :=
    SchwartzMap.fourierTransformCLM Complex v
  have hlowInterval : IntervalIntegrable
      (fun xi : Real =>
        suzukiSourceLogFourierWeight xi * ‖f xi‖ ^ 2)
      volume (-1) 1 := by
    apply intervalIntegrable_suzukiSourceLogFourierWeight.mul_continuousOn
    fun_prop
  have hlow : IntegrableOn
      (fun xi : Real =>
        suzukiSourceLogFourierWeight xi * ‖f xi‖ ^ 2)
      (Icc (-1) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1
      hlowInterval
  have hweightedMem := schwartz_memLp_suzukiLogWeighted f
  have hweightedPow := hweightedMem.integrable_norm_pow (by norm_num)
  have hmajor : Integrable
      (fun xi : Real =>
        suzukiLogFourierWeight xi * ‖f xi‖ ^ 2) := by
    apply hweightedPow.congr
    filter_upwards with xi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (suzukiLogFourierWeight_nonneg xi)]
  let C : Real :=
    abs (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant) + 1
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hmajorC : Integrable
      (fun xi : Real =>
        C * (suzukiLogFourierWeight xi * ‖f xi‖ ^ 2)) :=
    hmajor.const_mul C
  have hmeas : AEStronglyMeasurable
      (fun xi : Real =>
        suzukiSourceLogFourierWeight xi * ‖f xi‖ ^ 2) volume := by
    apply Measurable.aestronglyMeasurable
    unfold suzukiSourceLogFourierWeight
    fun_prop
  have hhigh : IntegrableOn
      (fun xi : Real =>
        suzukiSourceLogFourierWeight xi * ‖f xi‖ ^ 2)
      (Icc (-1) 1)ᶜ := by
    apply Integrable.mono' hmajorC.integrableOn hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with xi hxi
    have hout : 1 ≤ |xi| := by
      rw [mem_compl_iff, mem_Icc] at hxi
      rcases not_and_or.mp hxi with hleft | hright
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    have hweight := abs_suzukiSourceLogFourierWeight_le hout
    have hnormSq : 0 ≤ ‖f xi‖ ^ 2 := sq_nonneg _
    have hbound := mul_le_mul_of_nonneg_right hweight hnormSq
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hnormSq,
      abs_of_nonneg hC,
      abs_of_nonneg (suzukiLogFourierWeight_nonneg xi),
      C, mul_assoc] using hbound
  have hall := hlow.union hhigh
  simpa only [union_compl_self, integrableOn_univ, f] using hall

/-- The complex diagonal integrand of the polarized Fourier form is
integrable as the complexification of the real diagonal integrand. -/
theorem integrable_suzukiSourceLogFourierPolarizedSelfIntegrand
    (v : SchwartzLineTestFunction) :
    Integrable
      (fun xi : Real =>
        ((suzukiSourceLogFourierWeight xi : Real) : Complex) *
          (SchwartzMap.fourierTransformCLM Complex v xi *
            conj (SchwartzMap.fourierTransformCLM Complex v xi))) := by
  have hreal := integrable_suzukiSourceLogFourierFormIntegrand v
  have hcomplex : Integrable
      (fun xi : Real =>
        ((suzukiSourceLogFourierWeight xi *
          ‖SchwartzMap.fourierTransformCLM Complex v xi‖ ^ 2 : Real) :
            Complex)) :=
    hreal.ofReal
  apply hcomplex.congr
  filter_upwards with xi
  rw [Complex.mul_conj']
  norm_cast

/-- The real part of the diagonal polarized Fourier form is exactly the real
Fourier expression used in the source identity. -/
theorem suzukiSourceLogFourierPolarizedForm_self_re
    (v : SchwartzLineTestFunction) :
    (suzukiSourceLogFourierPolarizedForm v v).re =
      suzukiSourceLogFourierForm v := by
  have hint :=
    integrable_suzukiSourceLogFourierPolarizedSelfIntegrand v
  unfold suzukiSourceLogFourierPolarizedForm
    suzukiSourceLogFourierForm
  calc
    (∫ xi : Real,
        ((suzukiSourceLogFourierWeight xi : Real) : Complex) *
          (SchwartzMap.fourierTransformCLM Complex v xi *
            conj (SchwartzMap.fourierTransformCLM Complex v xi))).re =
        ∫ xi : Real,
          (((suzukiSourceLogFourierWeight xi : Real) : Complex) *
            (SchwartzMap.fourierTransformCLM Complex v xi *
              conj (SchwartzMap.fourierTransformCLM Complex v xi))).re :=
      (integral_re hint).symm
    _ = ∫ xi : Real,
        suzukiSourceLogFourierWeight xi *
          ‖SchwartzMap.fourierTransformCLM Complex v xi‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with xi
      rw [Complex.mul_conj']
      norm_cast

/-- The source identity to be proved on the exact Suzuki smooth core.  Naming
the proposition prevents a graph-energy surrogate from being confused with
the physical singular form. -/
def SuzukiSingularFourierIdentityAt (a : Real) : Prop :=
  ∀ v : SuzukiSmoothCore a,
    suzukiSingularLocalForm a v.1 =
      suzukiSourceLogFourierForm v.1

end

end M100
end Experiments
end RiemannHypothesisProject
