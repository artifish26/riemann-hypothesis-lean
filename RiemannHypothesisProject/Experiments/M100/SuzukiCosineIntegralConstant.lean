import RiemannHypothesisProject.Experiments.M100.SuzukiCosineIntegralAsymptotic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# M100-DF6D2 cosine-integral constant

This module develops the scalar special-function input left open by the
cutoff/Plancherel argument.  The first bridge identifies the logarithmic
exponential integral with the derivative of the Gamma function at one.  The
remaining comparison is between this exponential regularization and the
cosine regularization used by `suzukiCosineRegularConstant` and
`suzukiCosineTailConstant`.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

/-- The logarithmic Gamma-derivative integrand is genuinely integrable on the
positive half-line.  This is kept explicit because Bochner integrals are
totalized on nonintegrable functions. -/
theorem integrableOn_log_mul_exp_neg_Ioi :
    IntegrableOn (fun t : Real => Real.log t * Real.exp (-t)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · have hlog : IntegrableOn Real.log (Ioc (0 : Real) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        intervalIntegral.intervalIntegrable_log'
    apply hlog.mul_bdd
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1.le)
  · have hbase :
        IntegrableOn (fun t : Real => t * Real.exp (-t)) (Ioi 1) := by
      have h := integrableOn_rpow_mul_exp_neg_rpow
        (p := (1 : Real)) (s := (1 : Real)) (by norm_num) (by norm_num)
      have h' := h.mono_set
        (show Ioi (1 : Real) ⊆ Ioi 0 by
          intro t ht
          exact mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp ht)))
      simpa using h'
    apply hbase.mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := zero_lt_one.trans ht
      have hlogNonneg : 0 ≤ Real.log t := Real.log_nonneg ht.le
      have hlogLe : Real.log t ≤ t := by
        have := Real.log_le_sub_one_of_pos htpos
        linarith
      have hmul :=
        mul_le_mul_of_nonneg_right hlogLe (Real.exp_pos (-t)).le
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hlogNonneg (Real.exp_pos _).le),
        abs_of_nonneg (mul_nonneg htpos.le (Real.exp_pos _).le)] using hmul

/-- Exponential damping makes the cosine transform absolutely integrable. -/
theorem integrableOn_exp_neg_mul_cos
    {lam : Real} (hlam : 0 < lam) :
    IntegrableOn (fun t : Real => Real.exp (-lam * t) * Real.cos t) (Ioi 0) := by
  have hexp : IntegrableOn (fun t : Real => Real.exp (-lam * t)) (Ioi 0) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -lam) (neg_lt_zero.mpr hlam) 0)
  apply hexp.mul_bdd
  · fun_prop
  · filter_upwards with t
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one t

/-- The absolutely convergent Abel difference between cosine and the constant
mode. -/
def suzukiAbelCosineDifference (lam : Real) : Real :=
  ∫ t : Real in Ioi 0,
    Real.exp (-lam * t) * suzukiCosineRegularPart t

/-- Positive damping makes the regularized cosine difference genuinely
integrable on the whole positive half-line. -/
theorem integrableOn_suzukiAbelCosineDifference
    {lam : Real} (hlam : 0 < lam) :
    IntegrableOn
      (fun t : Real =>
        Real.exp (-lam * t) * suzukiCosineRegularPart t)
      (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · have hregular :
        IntegrableOn suzukiCosineRegularPart (Ioc (0 : Real) 1) :=
      integrableOn_suzukiCosineRegularPart.mono_set (by
        intro t ht
        exact ⟨by linarith [ht.1], ht.2⟩)
    apply hregular.bdd_mul
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam.le) ht.1.le)
  · have hexp : IntegrableOn (fun t : Real => Real.exp (-lam * t)) (Ioi 1) := by
      have h := integrableOn_exp_mul_Ioi (a := -lam) (neg_lt_zero.mpr hlam) 0
      have h' := h.mono_set
        (show Ioi (1 : Real) ⊆ Ioi 0 by
          intro t ht
          exact mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp ht)))
      simpa only [neg_mul] using h'
    apply hexp.mul_bdd
    · exact continuous_suzukiCosineRegularPart.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := zero_lt_one.trans ht
      unfold suzukiCosineRegularPart
      rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
      have hnum : abs (Real.cos t - 1) ≤ 2 := by
        calc
          abs (Real.cos t - 1) ≤ abs (Real.cos t) + abs (1 : Real) := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one t) (by norm_num)
          _ = 2 := by norm_num
      have htwo : (2 : Real) ≤ 2 * t := by
        nlinarith [mem_Ioi.mp ht]
      exact (div_le_iff₀ htpos).2 (hnum.trans htwo)

/-- Strong damping removes the Abel cosine difference. -/
theorem tendsto_suzukiAbelCosineDifference_atTop :
    Tendsto suzukiAbelCosineDifference atTop (nhds 0) := by
  let μ := volume.restrict (Ioi (0 : Real))
  let majorant : Real → Real := fun t =>
    ‖Real.exp (-t) * suzukiCosineRegularPart t‖
  have hmajorant : Integrable majorant μ := by
    simpa only [majorant, μ, neg_one_mul] using
      (integrableOn_suzukiAbelCosineDifference
        (lam := (1 : Real)) one_pos).norm
  have hmeas : ∀ᶠ lam : Real in atTop,
      AEStronglyMeasurable
        (fun t : Real =>
          Real.exp (-lam * t) * suzukiCosineRegularPart t) μ := by
    filter_upwards with lam
    have hlin : Continuous (fun t : Real => -lam * t) :=
      continuous_const.mul continuous_id
    exact ((Real.continuous_exp.comp hlin).mul
      continuous_suzukiCosineRegularPart).aestronglyMeasurable
  have hbound : ∀ᶠ lam : Real in atTop, ∀ᵐ t ∂μ,
      ‖Real.exp (-lam * t) * suzukiCosineRegularPart t‖ ≤ majorant t := by
    filter_upwards [eventually_ge_atTop (1 : Real)] with lam hlam
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := mem_Ioi.mp ht
    have hexpLe : Real.exp (-lam * t) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    dsimp only [majorant]
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hexpLe (abs_nonneg _)
  have hlimit : ∀ᵐ t ∂μ,
      Tendsto
        (fun lam : Real =>
          Real.exp (-lam * t) * suzukiCosineRegularPart t)
        atTop (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := mem_Ioi.mp ht
    have hexp :
        Tendsto (fun lam : Real => Real.exp (-lam * t)) atTop (nhds 0) := by
      have hbot : Tendsto (fun lam : Real => (-t) * lam) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr htpos)
      have hbot' : Tendsto (fun lam : Real => -lam * t) atTop atBot := by
        convert hbot using 1
        funext lam
        ring
      exact Real.tendsto_exp_atBot.comp hbot'
    simpa using hexp.mul_const (suzukiCosineRegularPart t)
  have hdct := tendsto_integral_filter_of_dominated_convergence
    majorant hmeas hbound hmajorant hlimit
  change Tendsto
    (fun lam : Real => ∫ t : Real in Ioi 0,
      Real.exp (-lam * t) * suzukiCosineRegularPart t)
    atTop (nhds 0)
  convert hdct using 1
  simp

/-- The elementary Laplace transform that drives the Abel comparison. -/
theorem integral_Ioi_exp_neg_mul_cos
    {lam : Real} (hlam : 0 < lam) :
    (∫ t : Real in Ioi 0, Real.exp (-lam * t) * Real.cos t) =
      lam / (lam ^ 2 + 1) := by
  let a : Complex := -(lam : Complex) + Complex.I
  have ha : a.re < 0 := by
    dsimp only [a]
    simp
    exact hlam
  have hint := integrableOn_exp_mul_complex_Ioi ha 0
  have heval := integral_exp_mul_complex_Ioi ha 0
  have hpoint (t : Real) :
      (Complex.exp (a * t)).re = Real.exp (-lam * t) * Real.cos t := by
    rw [Complex.exp_re]
    dsimp only [a]
    simp
  calc
    (∫ t : Real in Ioi 0, Real.exp (-lam * t) * Real.cos t) =
        ∫ t : Real in Ioi 0, (Complex.exp (a * t)).re := by
      apply integral_congr_ae
      filter_upwards with t
      exact (hpoint t).symm
    _ = (∫ t : Real in Ioi 0, Complex.exp (a * t)).re := integral_re hint
    _ = (-Complex.exp (a * 0) / a).re := congrArg Complex.re heval
    _ = lam / (lam ^ 2 + 1) := by
      dsimp only [a]
      simp [Complex.div_re, Complex.normSq]
      ring

/-- Subtracting the constant Laplace mode gives the derivative of the
Frullani comparison. -/
theorem integral_Ioi_exp_neg_mul_cos_sub_one
    {lam : Real} (hlam : 0 < lam) :
    (∫ t : Real in Ioi 0,
      Real.exp (-lam * t) * (Real.cos t - 1)) =
        lam / (lam ^ 2 + 1) - 1 / lam := by
  have hcos := integrableOn_exp_neg_mul_cos hlam
  have hexp : IntegrableOn (fun t : Real => Real.exp (-lam * t)) (Ioi 0) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -lam) (neg_lt_zero.mpr hlam) 0)
  calc
    (∫ t : Real in Ioi 0,
        Real.exp (-lam * t) * (Real.cos t - 1)) =
        (∫ t : Real in Ioi 0, Real.exp (-lam * t) * Real.cos t) -
          ∫ t : Real in Ioi 0, Real.exp (-lam * t) := by
      rw [← integral_sub hcos hexp]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = lam / (lam ^ 2 + 1) - 1 / lam := by
      rw [integral_Ioi_exp_neg_mul_cos hlam]
      have hexpEval := integral_exp_mul_Ioi
        (a := -lam) (neg_lt_zero.mpr hlam) 0
      simp only [mul_zero, Real.exp_zero, neg_div] at hexpEval
      have hexpEval' :
          (∫ t : Real in Ioi 0, Real.exp (-lam * t)) = 1 / lam := by
        calc
          _ = -(1 / -lam) := by simpa only [neg_mul] using hexpEval
          _ = 1 / lam := by
            field_simp [hlam.ne']
      rw [hexpEval']

/-- The product-space integrand used to integrate the Laplace parameter. -/
def suzukiAbelFubiniIntegrand (p : Real × Real) : Real :=
  Real.exp (-p.1 * p.2) * (Real.cos p.2 - 1)

/-- Uniform exponential decay gives the absolute integrability required for
the finite-parameter Fubini swap. -/
theorem integrable_suzukiAbelFubiniIntegrand
    {lam L : Real} (hlam : 0 < lam) :
    let μlam := volume.restrict (Ioc lam L)
    let μpos := volume.restrict (Ioi (0 : Real))
    Integrable suzukiAbelFubiniIntegrand (μlam.prod μpos) := by
  let μlam := volume.restrict (Ioc lam L)
  let μpos := volume.restrict (Ioi (0 : Real))
  have hconst : Integrable (fun _ : Real => (2 : Real)) μlam :=
    integrable_const 2
  have hexp : Integrable (fun t : Real => Real.exp (-lam * t)) μpos := by
    change IntegrableOn (fun t : Real => Real.exp (-lam * t)) (Ioi 0)
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -lam) (neg_lt_zero.mpr hlam) 0)
  have hmajorant : Integrable
      (fun p : Real × Real => 2 * Real.exp (-lam * p.2))
      (μlam.prod μpos) :=
    hconst.mul_prod hexp
  apply hmajorant.mono'
  · apply Continuous.aestronglyMeasurable
    unfold suzukiAbelFubiniIntegrand
    fun_prop
  · change ∀ᵐ p ∂((volume.restrict (Ioc lam L)).prod
        (volume.restrict (Ioi (0 : Real)))),
      ‖suzukiAbelFubiniIntegrand p‖ ≤ 2 * Real.exp (-lam * p.2)
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
    have hlamP : lam < p.1 := hp.1.1
    have htpos : 0 < p.2 := hp.2
    have hexpLe : Real.exp (-p.1 * p.2) ≤ Real.exp (-lam * p.2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hcos : abs (Real.cos p.2 - 1) ≤ 2 := by
      calc
        abs (Real.cos p.2 - 1) ≤
            abs (Real.cos p.2) + abs (1 : Real) := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one p.2) (by norm_num)
        _ = 2 := by norm_num
    rw [Real.norm_eq_abs, suzukiAbelFubiniIntegrand, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-p.1 * p.2) * abs (Real.cos p.2 - 1) ≤
          Real.exp (-p.1 * p.2) * 2 :=
        mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
      _ ≤ 2 * Real.exp (-lam * p.2) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hexpLe (by norm_num)

/-- Fubini exchanges the finite positive damping interval with the positive
spatial half-line. -/
theorem integral_Ioc_Ioi_suzukiAbelFubini_swap
    {lam L : Real} (hlam : 0 < lam) :
    (∫ r : Real in Ioc lam L,
        ∫ t : Real in Ioi 0,
          suzukiAbelFubiniIntegrand (r, t)) =
      ∫ t : Real in Ioi 0,
        ∫ r : Real in Ioc lam L,
          suzukiAbelFubiniIntegrand (r, t) := by
  let μlam := volume.restrict (Ioc lam L)
  let μpos := volume.restrict (Ioi (0 : Real))
  have hF : Integrable suzukiAbelFubiniIntegrand (μlam.prod μpos) := by
    simpa only [μlam, μpos] using
      (integrable_suzukiAbelFubiniIntegrand (L := L) hlam)
  have hF' : Integrable
      (Function.uncurry fun r t => suzukiAbelFubiniIntegrand (r, t))
      (μlam.prod μpos) := by
    apply hF.congr
    filter_upwards with p
    exact congrArg suzukiAbelFubiniIntegrand (Prod.eta p)
  simpa only [μlam, μpos] using integral_integral_swap hF'

/-- Integrating the Fubini kernel in the damping parameter gives the
difference of two damped regular-part integrands. -/
theorem intervalIntegral_suzukiAbelFubiniIntegrand
    {lam L t : Real} (ht : 0 < t) :
    (∫ r in lam..L, suzukiAbelFubiniIntegrand (r, t)) =
      (Real.exp (-lam * t) - Real.exp (-L * t)) *
        suzukiCosineRegularPart t := by
  let A : Real → Real := fun r =>
    (Real.cos t - 1) * (-(Real.exp (-t * r) / t))
  have hderiv (r : Real) (_hr : r ∈ [[lam, L]]) :
      HasDerivAt A (suzukiAbelFubiniIntegrand (r, t)) r := by
    have hlin : HasDerivAt (fun x : Real => -t * x) (-t) r := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id r).const_mul (-t)
    have hexp := (Real.hasDerivAt_exp (-t * r)).comp r hlin
    have hmain := (hexp.div_const t).neg.const_mul (Real.cos t - 1)
    refine hmain.congr_deriv ?_
    rw [show -t * r = -r * t by ring]
    unfold suzukiAbelFubiniIntegrand
    field_simp [ht.ne']
  have hint : IntervalIntegrable
      (fun r : Real => suzukiAbelFubiniIntegrand (r, t)) volume lam L := by
    apply Continuous.intervalIntegrable
    unfold suzukiAbelFubiniIntegrand
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [A]
  rw [show -t * L = -L * t by ring,
    show -t * lam = -lam * t by ring]
  unfold suzukiCosineRegularPart
  field_simp [ht.ne']
  ring

/-- The finite Frullani parameter integral is exactly the difference of two
Abel cosine differences. -/
theorem intervalIntegral_laplaceDerivative_eq_abelDifference_sub
    {lam L : Real} (hlam : 0 < lam) (hL : 0 < L) (hle : lam ≤ L) :
    (∫ r in lam..L, r / (r ^ 2 + 1) - 1 / r) =
      suzukiAbelCosineDifference lam - suzukiAbelCosineDifference L := by
  rw [intervalIntegral.integral_of_le hle]
  calc
    (∫ r : Real in Ioc lam L, r / (r ^ 2 + 1) - 1 / r) =
        ∫ r : Real in Ioc lam L,
          ∫ t : Real in Ioi 0,
            suzukiAbelFubiniIntegrand (r, t) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      have hrpos : 0 < r := hlam.trans hr.1
      simpa only [suzukiAbelFubiniIntegrand] using
        (integral_Ioi_exp_neg_mul_cos_sub_one hrpos).symm
    _ = ∫ t : Real in Ioi 0,
          ∫ r : Real in Ioc lam L,
            suzukiAbelFubiniIntegrand (r, t) :=
      integral_Ioc_Ioi_suzukiAbelFubini_swap (L := L) hlam
    _ = ∫ t : Real in Ioi 0,
          (Real.exp (-lam * t) - Real.exp (-L * t)) *
            suzukiCosineRegularPart t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (∫ r : Real in Ioc lam L,
          suzukiAbelFubiniIntegrand (r, t)) =
        (Real.exp (-lam * t) - Real.exp (-L * t)) *
          suzukiCosineRegularPart t
      rw [← intervalIntegral.integral_of_le hle]
      exact intervalIntegral_suzukiAbelFubiniIntegrand (mem_Ioi.mp ht)
    _ = suzukiAbelCosineDifference lam -
          suzukiAbelCosineDifference L := by
      have hlamInt := integrableOn_suzukiAbelCosineDifference hlam
      have hLInt := integrableOn_suzukiAbelCosineDifference hL
      unfold suzukiAbelCosineDifference
      rw [← integral_sub hlamInt hLInt]
      apply integral_congr_ae
      filter_upwards with t
      ring

/-- The closed-form Laplace transform has the logarithmic primitive required
for the Frullani parameter integral. -/
theorem hasDerivAt_half_log_sq_add_one (lam : Real) :
    HasDerivAt (fun x : Real => (1 / 2) * Real.log (x ^ 2 + 1))
      (lam / (lam ^ 2 + 1)) lam := by
  have hpos : 0 < lam ^ 2 + 1 := by positivity
  have h :=
    (((hasDerivAt_id lam).pow 2).add_const 1).log hpos.ne' |>.const_mul (1 / 2)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.one_apply, id_eq, pow_succ, pow_zero, mul_one]
  field_simp [hpos.ne']
  ring

/-- Primitive of the Laplace-transform difference appearing in the finite
Frullani identity. -/
def suzukiFrullaniPrimitive (x : Real) : Real :=
  (1 / 2) * Real.log (x ^ 2 + 1) - Real.log x

theorem hasDerivAt_suzukiFrullaniPrimitive
    {x : Real} (hx : 0 < x) :
    HasDerivAt suzukiFrullaniPrimitive
      (x / (x ^ 2 + 1) - 1 / x) x := by
  unfold suzukiFrullaniPrimitive
  have h := (hasDerivAt_half_log_sq_add_one x).sub
    (Real.hasDerivAt_log hx.ne')
  refine h.congr_deriv ?_
  simp only [one_div]

/-- Evaluation of the finite damping-parameter integral by its logarithmic
primitive. -/
theorem intervalIntegral_laplaceDerivative_eq_frullaniPrimitive_sub
    {lam L : Real} (hlam : 0 < lam) (hle : lam ≤ L) :
    (∫ r in lam..L, r / (r ^ 2 + 1) - 1 / r) =
      suzukiFrullaniPrimitive L - suzukiFrullaniPrimitive lam := by
  have hderiv (r : Real) (hr : r ∈ [[lam, L]]) :
      HasDerivAt suzukiFrullaniPrimitive
        (r / (r ^ 2 + 1) - 1 / r) r := by
    rw [uIcc_of_le hle] at hr
    exact hasDerivAt_suzukiFrullaniPrimitive (hlam.trans_le hr.1)
  have hint : IntervalIntegrable
      (fun r : Real => r / (r ^ 2 + 1) - 1 / r) volume lam L := by
    apply ContinuousOn.intervalIntegrable
    intro r hr
    rw [uIcc_of_le hle] at hr
    have hrpos : 0 < r := hlam.trans_le hr.1
    have hden : r ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg r]
    exact ((continuousAt_id.div
      ((continuousAt_id.pow 2).add continuousAt_const)
        hden).sub
      (continuousAt_const.div continuousAt_id hrpos.ne')).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Positive arguments rewrite the Frullani primitive in a form whose limit
at infinity is immediate. -/
theorem suzukiFrullaniPrimitive_eq_inv
    {x : Real} (hx : 0 < x) :
    suzukiFrullaniPrimitive x =
      (1 / 2) * Real.log (1 + (x⁻¹) ^ 2) := by
  unfold suzukiFrullaniPrimitive
  rw [show (1 / 2) * Real.log (x ^ 2 + 1) - Real.log x =
      (1 / 2) * (Real.log (x ^ 2 + 1) - 2 * Real.log x) by ring]
  have hlogpow : Real.log (x ^ 2) = 2 * Real.log x := by
    simpa using Real.log_pow x 2
  rw [← hlogpow, ← Real.log_div
    (by nlinarith [sq_nonneg x] : x ^ 2 + 1 ≠ 0)
    (pow_ne_zero 2 hx.ne')]
  congr 2
  field_simp [hx.ne']

theorem tendsto_suzukiFrullaniPrimitive_atTop :
    Tendsto suzukiFrullaniPrimitive atTop (nhds 0) := by
  have hinv : Tendsto (fun x : Real => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have harg :
      Tendsto (fun x : Real => 1 + (x⁻¹) ^ 2) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (hinv.pow 2)
  have hlog :
      Tendsto (fun x : Real => Real.log (1 + (x⁻¹) ^ 2))
        atTop (nhds 0) := by
    change Tendsto (Real.log ∘ fun x : Real => 1 + (x⁻¹) ^ 2)
      atTop (nhds 0)
    simpa only [Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : Real) ≠ 0)).tendsto.comp harg
  have hscaled :
      Tendsto (fun x : Real =>
        (1 / 2) * Real.log (1 + (x⁻¹) ^ 2)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlog
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  exact (suzukiFrullaniPrimitive_eq_inv hx).symm

/-- The damped cosine difference is exactly the negative Frullani primitive. -/
theorem suzukiAbelCosineDifference_eq_neg_frullaniPrimitive
    {lam : Real} (hlam : 0 < lam) :
    suzukiAbelCosineDifference lam = -suzukiFrullaniPrimitive lam := by
  have heq : ∀ᶠ L in atTop,
      suzukiAbelCosineDifference lam + suzukiFrullaniPrimitive lam =
        suzukiAbelCosineDifference L + suzukiFrullaniPrimitive L := by
    filter_upwards [eventually_ge_atTop lam, eventually_gt_atTop (0 : Real)]
      with L hle hL
    have hab := intervalIntegral_laplaceDerivative_eq_abelDifference_sub
      hlam hL hle
    have hfr := intervalIntegral_laplaceDerivative_eq_frullaniPrimitive_sub
      hlam hle
    linarith
  have hsum : Tendsto
      (fun L : Real =>
        suzukiAbelCosineDifference L + suzukiFrullaniPrimitive L)
      atTop (nhds 0) := by
    simpa using tendsto_suzukiAbelCosineDifference_atTop.add
      tendsto_suzukiFrullaniPrimitive_atTop
  have hconst : Tendsto
      (fun _L : Real =>
        suzukiAbelCosineDifference lam + suzukiFrullaniPrimitive lam)
      atTop (nhds 0) :=
    hsum.congr' (heq.mono fun _ h => h.symm)
  have hself : Tendsto
      (fun _L : Real =>
        suzukiAbelCosineDifference lam + suzukiFrullaniPrimitive lam)
      atTop (nhds
        (suzukiAbelCosineDifference lam + suzukiFrullaniPrimitive lam)) :=
    tendsto_const_nhds
  have hzero :
      suzukiAbelCosineDifference lam + suzukiFrullaniPrimitive lam = 0 :=
    tendsto_nhds_unique hself hconst
  linarith

/-- Closed logarithmic form of the damped cosine difference. -/
theorem suzukiAbelCosineDifference_eq_log_sub
    {lam : Real} (hlam : 0 < lam) :
    suzukiAbelCosineDifference lam =
      Real.log lam - (1 / 2) * Real.log (lam ^ 2 + 1) := by
  rw [suzukiAbelCosineDifference_eq_neg_frullaniPrimitive hlam]
  unfold suzukiFrullaniPrimitive
  ring

/-- The logarithmic exponential integral is the derivative of Gamma at one,
hence equals the negative Euler--Mascheroni constant. -/
theorem integral_Ioi_log_mul_exp_neg_eq_neg_eulerMascheroni :
    (∫ t : Real in Ioi 0, Real.log t * Real.exp (-t)) =
      -Real.eulerMascheroniConstant := by
  have hderivIntegral :=
    (Complex.hasDerivAt_GammaIntegral (s := (1 : Complex)) (by norm_num)).deriv
  have hopen : IsOpen {z : Complex | 0 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have heq : Complex.Gamma =ᶠ[nhds (1 : Complex)] Complex.GammaIntegral := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  have hcomplex :
      (∫ t : Real in Ioi 0,
          t ^ ((1 : Complex) - 1) *
            ((Real.log t : Complex) * (Real.exp (-t) : Complex))) =
        -(Real.eulerMascheroniConstant : Complex) := by
    rw [← hderivIntegral, ← heq.deriv_eq]
    simpa using Complex.hasDerivAt_Gamma_one.deriv
  have hcast :
      (∫ t : Real in Ioi 0,
          t ^ ((1 : Complex) - 1) *
            ((Real.log t : Complex) * (Real.exp (-t) : Complex))) =
        Complex.ofReal
          (∫ t : Real in Ioi 0, Real.log t * Real.exp (-t)) := by
    calc
      _ = ∫ t : Real in Ioi 0,
          ((Real.log t * Real.exp (-t) : Real) : Complex) := by
        apply integral_congr_ae
        filter_upwards with t
        simp
      _ = Complex.ofReal (∫ t : Real in Ioi 0,
          Real.log t * Real.exp (-t)) := integral_ofReal
  rw [hcast] at hcomplex
  exact_mod_cast hcomplex

/-- The near-zero part of the exponentially normalized reciprocal integral. -/
def suzukiExponentialRegularPart (lam t : Real) : Real :=
  (Real.exp (-lam * t) - 1) / t

/-- The exponentially normalized reciprocal integral, split at one so that
both pieces are absolutely integrable. -/
def suzukiExponentialNormalizedConstant (lam : Real) : Real :=
  (∫ t in (0 : Real)..1, suzukiExponentialRegularPart lam t) +
    ∫ t : Real in Ioi 1, Real.exp (-lam * t) / t

theorem integrableOn_suzukiExponentialRegularPart
    {lam : Real} (hlam : 0 < lam) :
    IntegrableOn (suzukiExponentialRegularPart lam) (Ioc 0 1) := by
  apply Measure.integrableOn_of_bounded
    (M := lam) measure_Ioc_lt_top.ne
  · apply Measurable.aestronglyMeasurable
    unfold suzukiExponentialRegularPart
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ht.1
    have hexpLe : Real.exp (-lam * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hdiff : 1 - Real.exp (-lam * t) ≤ lam * t := by
      linarith [Real.add_one_le_exp (-lam * t)]
    rw [Real.norm_eq_abs, suzukiExponentialRegularPart, abs_div,
      abs_of_pos htpos, abs_of_nonpos (sub_nonpos.mpr hexpLe)]
    apply (div_le_iff₀ htpos).2
    linarith

theorem integrableOn_exp_neg_div_Ioi_one
    {lam : Real} (hlam : 0 < lam) :
    IntegrableOn (fun t : Real => Real.exp (-lam * t) / t) (Ioi 1) := by
  have hexp : IntegrableOn (fun t : Real => Real.exp (-lam * t)) (Ioi 1) := by
    have h := integrableOn_exp_mul_Ioi
      (a := -lam) (neg_lt_zero.mpr hlam) 0
    exact (by
      simpa only [neg_mul] using h.mono_set
        (show Ioi (1 : Real) ⊆ Ioi 0 by
          intro t ht
          exact mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp ht))))
  change IntegrableOn
    (fun t : Real => Real.exp (-lam * t) * t⁻¹) (Ioi 1)
  apply hexp.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos)]
    exact inv_le_one_of_one_le₀ ht.le

/-- Scaling the logarithmic Gamma integral introduces exactly `-log lam`. -/
theorem integral_Ioi_lam_mul_log_mul_exp_neg
    {lam : Real} (hlam : 0 < lam) :
    (∫ t : Real in Ioi 0,
        lam * (Real.log t * Real.exp (-lam * t))) =
      -Real.eulerMascheroniConstant - Real.log lam := by
  let g : Real → Real := fun u =>
    (Real.log u - Real.log lam) * Real.exp (-u)
  have hscale := integral_comp_mul_left_Ioi g 0 hlam
  have hpoint (t : Real) (ht : t ∈ Ioi (0 : Real)) :
      g (lam * t) = Real.log t * Real.exp (-lam * t) := by
    dsimp only [g]
    rw [Real.log_mul hlam.ne' (mem_Ioi.mp ht).ne']
    ring
  have hscaled :
      (∫ t : Real in Ioi 0, g (lam * t)) =
        lam⁻¹ * ∫ u : Real in Ioi 0, g u := by
    simpa only [mul_zero, smul_eq_mul] using hscale
  calc
    (∫ t : Real in Ioi 0,
        lam * (Real.log t * Real.exp (-lam * t))) =
        lam * ∫ t : Real in Ioi 0,
          Real.log t * Real.exp (-lam * t) := by
      rw [integral_const_mul]
    _ = lam * ∫ t : Real in Ioi 0, g (lam * t) := by
      exact congrArg (fun x : Real => lam * x)
        (setIntegral_congr_fun measurableSet_Ioi
          (fun t ht => (hpoint t ht).symm))
    _ = ∫ u : Real in Ioi 0, g u := by
      rw [hscaled]
      field_simp [hlam.ne']
    _ = (∫ u : Real in Ioi 0,
          Real.log u * Real.exp (-u)) -
        Real.log lam * ∫ u : Real in Ioi 0, Real.exp (-u) := by
      have hlog := integrableOn_log_mul_exp_neg_Ioi
      have hexp : IntegrableOn (fun u : Real => Real.exp (-u)) (Ioi 0) := by
        simpa only [neg_one_mul] using
          (integrableOn_exp_mul_Ioi (a := (-1 : Real)) (by norm_num) 0)
      calc
        (∫ u : Real in Ioi 0, g u) =
            ∫ u : Real in Ioi 0,
              Real.log u * Real.exp (-u) -
                Real.log lam * Real.exp (-u) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          unfold g
          ring
        _ = (∫ u : Real in Ioi 0,
              Real.log u * Real.exp (-u)) -
            ∫ u : Real in Ioi 0,
              Real.log lam * Real.exp (-u) := integral_sub hlog
                (hexp.const_mul (Real.log lam))
        _ = (∫ u : Real in Ioi 0,
              Real.log u * Real.exp (-u)) -
            Real.log lam * ∫ u : Real in Ioi 0, Real.exp (-u) := by
          rw [integral_const_mul]
    _ = -Real.eulerMascheroniConstant - Real.log lam := by
      rw [integral_Ioi_log_mul_exp_neg_eq_neg_eulerMascheroni]
      have hexpEval := integral_exp_mul_Ioi
        (a := (-1 : Real)) (by norm_num) 0
      norm_num at hexpEval ⊢
      rw [hexpEval]
      ring

theorem integrableOn_lam_mul_log_mul_exp_neg
    {lam : Real} (hlam : 0 < lam) :
    IntegrableOn
      (fun t : Real => lam * (Real.log t * Real.exp (-lam * t)))
      (Ioi 0) := by
  let g : Real → Real := fun u =>
    (Real.log u - Real.log lam) * Real.exp (-u)
  have hlog := integrableOn_log_mul_exp_neg_Ioi
  have hexp : IntegrableOn (fun u : Real => Real.exp (-u)) (Ioi 0) := by
    simpa only [neg_one_mul] using
      (integrableOn_exp_mul_Ioi (a := (-1 : Real)) (by norm_num) 0)
  have hg : IntegrableOn g (Ioi 0) := by
    have hsub := hlog.sub (hexp.const_mul (Real.log lam))
    apply hsub.congr
    filter_upwards with u
    unfold g
    simp only [Pi.sub_apply]
    ring
  have hcomp : IntegrableOn (fun t : Real => g (lam * t)) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff g 0 hlam).2 (by simpa using hg)
  apply (hcomp.const_mul lam).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  dsimp only [g]
  rw [Real.log_mul hlam.ne' (mem_Ioi.mp ht).ne']
  ring

/-- An integrable function on `(0,1]` may be recovered from positive lower
cutoffs tending to zero. -/
theorem tendsto_intervalIntegral_zero_one_of_integrableOn_Ioc
    {f : Real → Real} (hf : IntegrableOn f (Ioc 0 1)) :
    Tendsto (fun s : Real => ∫ t in s..1, f t) (𝓝[>] (0 : Real))
      (nhds (∫ t in (0 : Real)..1, f t)) := by
  have hcont : ContinuousOn (fun s : Real => ∫ t in s..1, f t)
      (uIcc (0 : Real) 1) :=
    intervalIntegral.continuousOn_primitive_interval_left
      (by
        rw [uIcc_of_le zero_le_one]
        exact hf.congr_set_ae Ioc_ae_eq_Icc.symm)
  have hzero : (0 : Real) ∈ uIcc (0 : Real) 1 := by
    rw [uIcc_of_le zero_le_one]
    exact ⟨le_rfl, zero_le_one⟩
  have htend := (hcont 0 hzero).tendsto
  apply htend.mono_left
  rw [uIcc_of_le zero_le_one, nhdsWithin, nhdsWithin, le_inf_iff]
  constructor
  · exact inf_le_left
  · rw [le_principal_iff]
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Iio (1 : Real), Iio_mem_nhds (by norm_num), ?_⟩
    intro s hs
    exact ⟨hs.2.le, hs.1.le⟩

/-- Finite-interval integration by parts for the scaled Gamma derivative. -/
theorem intervalIntegral_lam_log_exp_eq_boundary_add
    {lam a b : Real} (hlam : 0 < lam) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, lam * (Real.log t * Real.exp (-lam * t))) =
      -Real.log b * Real.exp (-lam * b) +
        Real.log a * Real.exp (-lam * a) +
        ∫ t in a..b, Real.exp (-lam * t) / t := by
  let F : Real → Real := fun t => -Real.log t * Real.exp (-lam * t)
  have hpos {t : Real} (ht : t ∈ [[a, b]]) : 0 < t := by
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hderiv (t : Real) (ht : t ∈ [[a, b]]) :
      HasDerivAt F
        (lam * (Real.log t * Real.exp (-lam * t)) -
          Real.exp (-lam * t) / t) t := by
    have htpos := hpos ht
    have hlin : HasDerivAt (fun x : Real => -lam * x) (-lam) t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (-lam)
    have hexp := (Real.hasDerivAt_exp (-lam * t)).comp t hlin
    have hmain := (Real.hasDerivAt_log htpos.ne').neg.mul hexp
    unfold F
    refine hmain.congr_deriv ?_
    simp only [Pi.neg_apply, Function.comp_apply]
    field_simp [htpos.ne']
    ring
  have hint : IntervalIntegrable
      (fun t : Real =>
        lam * (Real.log t * Real.exp (-lam * t)) -
          Real.exp (-lam * t) / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htpos := hpos ht
    exact ((continuousAt_const.mul
      ((Real.continuousAt_log htpos.ne').mul
        (Real.continuous_exp.continuousAt.comp
          (continuousAt_const.mul continuousAt_id)))).sub
      ((Real.continuous_exp.continuousAt.comp
        (continuousAt_const.mul continuousAt_id)).div
        continuousAt_id htpos.ne')).continuousWithinAt
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hgamma : IntervalIntegrable
      (fun t : Real => lam * (Real.log t * Real.exp (-lam * t)))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htpos := hpos ht
    exact (continuousAt_const.mul
      ((Real.continuousAt_log htpos.ne').mul
        (Real.continuous_exp.continuousAt.comp
          (continuousAt_const.mul continuousAt_id)))).continuousWithinAt
  have hexpdiv : IntervalIntegrable
      (fun t : Real => Real.exp (-lam * t) / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htpos := hpos ht
    exact ((Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)).div
        continuousAt_id htpos.ne').continuousWithinAt
  rw [intervalIntegral.integral_sub hgamma hexpdiv] at hfund
  dsimp only [F] at hfund
  linarith

theorem tendsto_log_mul_one_sub_exp_neg_mul
    {lam : Real} :
    Tendsto (fun s : Real =>
        Real.log s * (1 - Real.exp (-lam * s)))
      (𝓝[>] (0 : Real)) (nhds 0) := by
  have hlin : HasDerivAt (fun s : Real => -lam * s) (-lam) 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id 0).const_mul (-lam)
  have hexp := (Real.hasDerivAt_exp (-lam * 0)).comp 0 hlin
  have hderiv : HasDerivAt
      (fun s : Real => 1 - Real.exp (-lam * s)) lam 0 := by
    have hraw :=
      (hasDerivAt_const (x := (0 : Real)) (c := (1 : Real))).sub hexp
    have heq : (fun s : Real => 1 - Real.exp (-lam * s)) =ᶠ[nhds 0]
        ((fun _s : Real => (1 : Real)) -
          (Real.exp ∘ fun s : Real => -lam * s)) := by
      filter_upwards with s
      rfl
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv (by simp)
  have hslope : Tendsto
      (fun s : Real => (1 - Real.exp (-lam * s)) / s)
      (𝓝[>] (0 : Real)) (nhds lam) := by
    simpa only [zero_add, mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero,
      smul_eq_mul, inv_mul_eq_div] using hderiv.tendsto_slope_zero_right
  have hlogself : Tendsto (fun s : Real => Real.log s * s)
      (𝓝[>] (0 : Real)) (nhds 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one)
  have hprod := hlogself.mul hslope
  simpa using hprod.congr' (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos := mem_Ioi.mp hs
    field_simp [hspos.ne'])

/-- At a positive lower cutoff, the regularized exponential integral differs
from the scaled Gamma integral only by a vanishing endpoint term. -/
theorem intervalIntegral_suzukiExponentialRegularPart_eq_gamma_add
    {lam s : Real} (hlam : 0 < lam) (hs : 0 < s) (hsOne : s ≤ 1) :
    (∫ t in s..1, suzukiExponentialRegularPart lam t) =
      (∫ t in s..1,
        lam * (Real.log t * Real.exp (-lam * t))) +
        Real.log s * (1 - Real.exp (-lam * s)) := by
  have hexpdiv : IntervalIntegrable
      (fun t : Real => Real.exp (-lam * t) / t) volume s 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hsOne] at ht
    have htpos : 0 < t := hs.trans_le ht.1
    exact ((Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)).div
        continuousAt_id htpos.ne').continuousWithinAt
  have hinv : IntervalIntegrable (fun t : Real => 1 / t) volume s 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hsOne] at ht
    have htpos : 0 < t := hs.trans_le ht.1
    exact (continuousAt_const.div continuousAt_id htpos.ne').continuousWithinAt
  have hregular :
      (∫ t in s..1, suzukiExponentialRegularPart lam t) =
        (∫ t in s..1, Real.exp (-lam * t) / t) -
          ∫ t in s..1, 1 / t := by
    rw [← intervalIntegral.integral_sub hexpdiv hinv]
    apply intervalIntegral.integral_congr
    intro t ht
    unfold suzukiExponentialRegularPart
    ring
  have hinvValue : (∫ t in s..1, 1 / t) = -Real.log s := by
    calc
      (∫ t in s..1, 1 / t) = Real.log ((1 : Real) / s) := by
        simpa only [one_div] using integral_inv_of_pos hs zero_lt_one
      _ = -Real.log s := by
        rw [show (1 : Real) / s = s⁻¹ by simp]
        exact Real.log_inv s
  have hparts := intervalIntegral_lam_log_exp_eq_boundary_add
    hlam hs hsOne
  simp only [Real.log_one, neg_zero, zero_mul, zero_add] at hparts
  rw [hregular, hinvValue]
  linarith

/-- The near-zero exponential normalization is the near-zero piece of the
scaled logarithmic Gamma integral. -/
theorem integral_zero_one_suzukiExponentialRegularPart_eq_gamma
    {lam : Real} (hlam : 0 < lam) :
    (∫ t in (0 : Real)..1, suzukiExponentialRegularPart lam t) =
      ∫ t in (0 : Real)..1,
        lam * (Real.log t * Real.exp (-lam * t)) := by
  have hreg := tendsto_intervalIntegral_zero_one_of_integrableOn_Ioc
    (integrableOn_suzukiExponentialRegularPart hlam)
  have hgammaInt : IntegrableOn
      (fun t : Real => lam * (Real.log t * Real.exp (-lam * t)))
      (Ioc 0 1) :=
    (integrableOn_lam_mul_log_mul_exp_neg hlam).mono_set (by
      intro t ht
      exact mem_Ioi.mpr ht.1)
  have hgamma :=
    tendsto_intervalIntegral_zero_one_of_integrableOn_Ioc hgammaInt
  have hsum := hgamma.add
    (tendsto_log_mul_one_sub_exp_neg_mul (lam := lam))
  have heq : ∀ᶠ s in 𝓝[>] (0 : Real),
      (∫ t in s..1, suzukiExponentialRegularPart lam t) =
        (∫ t in s..1,
          lam * (Real.log t * Real.exp (-lam * t))) +
          Real.log s * (1 - Real.exp (-lam * s)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Iio (1 : Real), Iio_mem_nhds (by norm_num), Subset.rfl⟩]
      with s hs hsOne
    exact intervalIntegral_suzukiExponentialRegularPart_eq_gamma_add
      hlam (mem_Ioi.mp hs) (mem_Iio.mp hsOne.1).le
  have hsum' : Tendsto
      (fun s : Real =>
        (∫ t in s..1,
          lam * (Real.log t * Real.exp (-lam * t))) +
          Real.log s * (1 - Real.exp (-lam * s)))
      (𝓝[>] (0 : Real))
      (nhds (∫ t in (0 : Real)..1,
        lam * (Real.log t * Real.exp (-lam * t)))) := by
    simpa using hsum
  exact tendsto_nhds_unique hreg
    (hsum'.congr' (heq.mono fun _ h => h.symm))

/-- Logarithmic growth is dominated by every positive exponential decay. -/
theorem tendsto_log_mul_exp_neg_mul_atTop
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (fun R : Real => Real.log R * Real.exp (-lam * R))
      atTop (nhds 0) := by
  have hupper : Tendsto (fun R : Real => R * Real.exp (-lam * R))
      atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 lam hlam)
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : Real)] with R hR
    exact mul_nonneg (Real.log_nonneg hR) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : Real)] with R hR
    have hlogLe : Real.log R ≤ R := by
      linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hR)]
    exact mul_le_mul_of_nonneg_right hlogLe (Real.exp_pos _).le
  · exact hupper

/-- The exponentially decaying tail is the tail of the scaled Gamma
derivative after integration by parts. -/
theorem integral_Ioi_exp_neg_div_eq_gamma
    {lam : Real} (hlam : 0 < lam) :
    (∫ t : Real in Ioi 1, Real.exp (-lam * t) / t) =
      ∫ t : Real in Ioi 1,
        lam * (Real.log t * Real.exp (-lam * t)) := by
  have hexp := integrableOn_exp_neg_div_Ioi_one hlam
  have hgamma : IntegrableOn
      (fun t : Real => lam * (Real.log t * Real.exp (-lam * t)))
      (Ioi 1) :=
    (integrableOn_lam_mul_log_mul_exp_neg hlam).mono_set (by
      intro t ht
      exact mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp ht)))
  have hexpLim := intervalIntegral_tendsto_integral_Ioi
    (a := (1 : Real)) hexp tendsto_id
  have hgammaLim := intervalIntegral_tendsto_integral_Ioi
    (a := (1 : Real)) hgamma tendsto_id
  have hboundaryRaw := (tendsto_log_mul_exp_neg_mul_atTop hlam).neg
  have hboundary : Tendsto
      (fun R : Real => -Real.log R * Real.exp (-lam * R))
      atTop (nhds 0) := by
    have hboundary' : Tendsto
        (fun R : Real => -Real.log R * Real.exp (-lam * R))
        atTop (nhds (-0)) := by
      apply hboundaryRaw.congr'
      filter_upwards with R
      ring
    simpa using hboundary'
  have hsum := hboundary.add hexpLim
  have heq : ∀ᶠ R in atTop,
      (∫ t in (1 : Real)..R,
        lam * (Real.log t * Real.exp (-lam * t))) =
        -Real.log R * Real.exp (-lam * R) +
          ∫ t in (1 : Real)..R, Real.exp (-lam * t) / t := by
    filter_upwards [eventually_ge_atTop (1 : Real)] with R hR
    simpa only [Real.log_one, neg_zero, zero_mul, zero_add, add_zero] using
      intervalIntegral_lam_log_exp_eq_boundary_add
        hlam zero_lt_one hR
  have hsum' : Tendsto
      (fun R : Real =>
        -Real.log R * Real.exp (-lam * R) +
          ∫ t in (1 : Real)..R, Real.exp (-lam * t) / t)
      atTop (nhds (∫ t : Real in Ioi 1,
        Real.exp (-lam * t) / t)) := by
    simpa only [id_eq, zero_add] using hsum
  have hgammaAsSum := hsum'.congr' (heq.mono fun _ h => h.symm)
  exact (tendsto_nhds_unique hgammaLim hgammaAsSum).symm

/-- Exact evaluation of the split exponential normalization. -/
theorem suzukiExponentialNormalizedConstant_eq
    {lam : Real} (hlam : 0 < lam) :
    suzukiExponentialNormalizedConstant lam =
      -Real.eulerMascheroniConstant - Real.log lam := by
  have hglobal := integral_Ioi_lam_mul_log_mul_exp_neg hlam
  have hgamma := integrableOn_lam_mul_log_mul_exp_neg hlam
  have hlocal : IntegrableOn
      (fun t : Real => lam * (Real.log t * Real.exp (-lam * t)))
      (Ioc 0 1) := hgamma.mono_set (by
        intro t ht
        exact mem_Ioi.mpr ht.1)
  have htail : IntegrableOn
      (fun t : Real => lam * (Real.log t * Real.exp (-lam * t)))
      (Ioi 1) := hgamma.mono_set (by
        intro t ht
        exact mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp ht)))
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi_same)
    measurableSet_Ioi hlocal htail
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  unfold suzukiExponentialNormalizedConstant
  rw [integral_zero_one_suzukiExponentialRegularPart_eq_gamma hlam,
    integral_Ioi_exp_neg_div_eq_gamma hlam]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [← hsplit]
  exact hglobal

/-- The normalized Abel value is assembled from the absolutely convergent
cosine difference and exponential normalization. -/
def suzukiAbelCosineNormalizedConstant (lam : Real) : Real :=
  suzukiAbelCosineDifference lam +
    suzukiExponentialNormalizedConstant lam

/-- Exact damped cosine value.  The `log lam` terms from the Frullani and
Gamma pieces cancel. -/
theorem suzukiAbelCosineNormalizedConstant_eq
    {lam : Real} (hlam : 0 < lam) :
    suzukiAbelCosineNormalizedConstant lam =
      -Real.eulerMascheroniConstant -
        (1 / 2) * Real.log (lam ^ 2 + 1) := by
  unfold suzukiAbelCosineNormalizedConstant
  rw [suzukiAbelCosineDifference_eq_log_sub hlam,
    suzukiExponentialNormalizedConstant_eq hlam]
  ring

/-- The damped oscillatory tail is absolutely integrable. -/
theorem integrableOn_exp_neg_mul_cos_div_Ioi_one
    {lam : Real} (hlam : 0 < lam) :
    IntegrableOn
      (fun t : Real => Real.exp (-lam * t) * Real.cos t / t)
      (Ioi 1) := by
  have hbase := (integrableOn_exp_neg_mul_cos hlam).mono_set (by
    intro t ht
    exact mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp ht)))
  change IntegrableOn
    (fun t : Real =>
      (Real.exp (-lam * t) * Real.cos t) * t⁻¹) (Ioi 1)
  apply hbase.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos)]
    exact inv_le_one_of_one_le₀ ht.le

/-- The Abel-normalized value is the sum of a regular near-zero integral and
an absolutely convergent damped oscillatory tail. -/
theorem suzukiAbelCosineNormalizedConstant_eq_regular_add_tail
    {lam : Real} (hlam : 0 < lam) :
    suzukiAbelCosineNormalizedConstant lam =
      (∫ t in (0 : Real)..1,
        Real.exp (-lam * t) * suzukiCosineRegularPart t +
          suzukiExponentialRegularPart lam t) +
        ∫ t : Real in Ioi 1,
          Real.exp (-lam * t) * Real.cos t / t := by
  have hdiff := integrableOn_suzukiAbelCosineDifference hlam
  have hdiffLocal : IntegrableOn
      (fun t : Real =>
        Real.exp (-lam * t) * suzukiCosineRegularPart t)
      (Ioc 0 1) := hdiff.mono_set (by
    intro t ht
    exact mem_Ioi.mpr ht.1)
  have hdiffTail : IntegrableOn
      (fun t : Real =>
        Real.exp (-lam * t) * suzukiCosineRegularPart t)
      (Ioi 1) := hdiff.mono_set (by
    intro t ht
    exact mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp ht)))
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi hdiffLocal hdiffTail
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  have hlocalExp := integrableOn_suzukiExponentialRegularPart hlam
  have htailExp := integrableOn_exp_neg_div_Ioi_one hlam
  have htailCos := integrableOn_exp_neg_mul_cos_div_Ioi_one hlam
  unfold suzukiAbelCosineNormalizedConstant
    suzukiAbelCosineDifference suzukiExponentialNormalizedConstant
  rw [hsplit, intervalIntegral.integral_of_le zero_le_one,
    add_add_add_comm,
    ← integral_add hdiffLocal hlocalExp,
    ← integral_add hdiffTail htailExp]
  rw [intervalIntegral.integral_of_le zero_le_one]
  apply congrArg₂ (.+.)
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    ring
  · exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      have htpos : 0 < t := zero_lt_one.trans (mem_Ioi.mp ht)
      unfold suzukiCosineRegularPart
      field_simp [htpos.ne']
      ring)

/-- The regular near-zero part of the Abel normalization converges by
dominated convergence. -/
theorem tendsto_suzukiAbelCosineRegularIntegral :
    Tendsto
      (fun lam : Real => ∫ t in (0 : Real)..1,
        Real.exp (-lam * t) * suzukiCosineRegularPart t +
          suzukiExponentialRegularPart lam t)
      (𝓝[>] (0 : Real)) (nhds suzukiCosineRegularConstant) := by
  let μ := volume.restrict (Ioc (0 : Real) 1)
  let majorant : Real → Real := fun t =>
    ‖suzukiCosineRegularPart t‖ + 1
  have hmajorant : Integrable majorant μ := by
    have hreg : Integrable suzukiCosineRegularPart μ := by
      change IntegrableOn suzukiCosineRegularPart (Ioc 0 1)
      exact integrableOn_suzukiCosineRegularPart.mono_set (by
        intro t ht
        exact ⟨by linarith [ht.1], ht.2⟩)
    exact hreg.norm.add (integrable_const 1)
  have hmeas : ∀ᶠ lam : Real in 𝓝[>] (0 : Real),
      AEStronglyMeasurable
        (fun t : Real =>
          Real.exp (-lam * t) * suzukiCosineRegularPart t +
            suzukiExponentialRegularPart lam t) μ := by
    filter_upwards with lam
    apply Measurable.aestronglyMeasurable
    unfold suzukiExponentialRegularPart suzukiCosineRegularPart
    fun_prop
  have hbound : ∀ᶠ lam : Real in 𝓝[>] (0 : Real), ∀ᵐ t ∂μ,
      ‖Real.exp (-lam * t) * suzukiCosineRegularPart t +
          suzukiExponentialRegularPart lam t‖ ≤ majorant t := by
    have hOne : Iio (1 : Real) ∈ 𝓝[>] (0 : Real) :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Iio (1 : Real), Iio_mem_nhds (by norm_num), inter_subset_left⟩
    filter_upwards [self_mem_nhdsWithin, hOne] with lam hlam hlamOne
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ht.1
    have hexpLe : Real.exp (-lam * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mem_Ioi.mp hlam])
    have hfirst :
        ‖Real.exp (-lam * t) * suzukiCosineRegularPart t‖ ≤
          ‖suzukiCosineRegularPart t‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hexpLe (norm_nonneg _)
    have hdiff : 1 - Real.exp (-lam * t) ≤ lam * t := by
      linarith [Real.add_one_le_exp (-lam * t)]
    have hsecond : ‖suzukiExponentialRegularPart lam t‖ ≤ 1 := by
      have hexpOne : Real.exp (-lam * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [mem_Ioi.mp hlam])
      rw [Real.norm_eq_abs, suzukiExponentialRegularPart, abs_div,
        abs_of_pos htpos, abs_of_nonpos (sub_nonpos.mpr hexpOne)]
      apply (div_le_iff₀ htpos).2
      have hlamLe : lam ≤ 1 := (mem_Iio.mp hlamOne).le
      nlinarith
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  have hlimit : ∀ᵐ t ∂μ,
      Tendsto
        (fun lam : Real =>
          Real.exp (-lam * t) * suzukiCosineRegularPart t +
            suzukiExponentialRegularPart lam t)
        (𝓝[>] (0 : Real)) (nhds (suzukiCosineRegularPart t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ht.1
    have hexp : Tendsto (fun lam : Real => Real.exp (-lam * t))
        (𝓝[>] (0 : Real)) (nhds 1) := by
      have hlin : Tendsto (fun lam : Real => -lam * t)
          (𝓝[>] (0 : Real)) (nhds 0) := by
        have hn : ContinuousAt (fun lam : Real => -lam) 0 :=
          continuousAt_id.neg
        have hc : ContinuousAt (fun _lam : Real => t) 0 :=
          continuousAt_const
        have hrestricted : Tendsto
            ((fun lam : Real => -lam) * fun _lam : Real => t)
            (𝓝[>] (0 : Real)) (nhds 0) := by
          simpa using (hn.mul hc).tendsto.mono_left
            (show 𝓝[>] (0 : Real) ≤ nhds 0 from inf_le_left)
        exact hrestricted.congr' (Eventually.of_forall fun lam => by
          simp only [Pi.mul_apply])
      change Tendsto (Real.exp ∘ fun lam : Real => -lam * t)
        (𝓝[>] (0 : Real)) (nhds 1)
      simpa only [Real.exp_zero] using
        Real.continuous_exp.continuousAt.tendsto.comp hlin
    have hregular : Tendsto (fun lam : Real =>
        suzukiExponentialRegularPart lam t)
        (𝓝[>] (0 : Real)) (nhds 0) := by
      unfold suzukiExponentialRegularPart
      have hone : Tendsto (fun _lam : Real => (1 : Real))
          (𝓝[>] (0 : Real)) (nhds 1) := tendsto_const_nhds
      have hnum : Tendsto (fun lam : Real => Real.exp (-lam * t) - 1)
          (𝓝[>] (0 : Real)) (nhds 0) := by
        simpa using hexp.sub hone
      simpa using hnum.div_const t
    simpa using (hexp.mul_const (suzukiCosineRegularPart t)).add hregular
  have hdct := tendsto_integral_filter_of_dominated_convergence
    majorant hmeas hbound hmajorant hlimit
  change Tendsto
      (fun lam : Real => ∫ t : Real in Ioc 0 1,
        Real.exp (-lam * t) * suzukiCosineRegularPart t +
          suzukiExponentialRegularPart lam t)
      (𝓝[>] (0 : Real))
      (nhds (∫ t : Real in Ioc 0 1, suzukiCosineRegularPart t)) at hdct
  unfold suzukiCosineRegularConstant
  simpa only [intervalIntegral.integral_of_le zero_le_one] using hdct

/-- The real-cutoff cosine-tail primitive has the expected derivative at
every point at or to the right of its base point. -/
theorem hasDerivAt_suzukiCosineTailPartialReal
    {R : Real} (hR : 1 ≤ R) :
    HasDerivAt suzukiCosineTailPartialReal (Real.cos R / R) R := by
  have hRne : R ≠ 0 := (zero_lt_one.trans_le hR).ne'
  have hcont : ContinuousAt (fun t : Real => Real.cos t / t) R :=
    Real.continuous_cos.continuousAt.div continuousAt_id hRne
  unfold suzukiCosineTailPartialReal
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_cos_div_of_one_le (le_refl (1 : Real)) hR)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun x hx => Real.continuous_cos.continuousAt.div continuousAt_id
        (mem_Ioi.mp hx).ne') R (zero_lt_one.trans_le hR))
    hcont

/-- The real-cutoff cosine-tail primitive is continuous on `[1, ∞)`. -/
theorem continuousOn_suzukiCosineTailPartialReal :
    ContinuousOn suzukiCosineTailPartialReal (Ici (1 : Real)) := by
  intro R hR
  exact (hasDerivAt_suzukiCosineTailPartialReal hR).continuousAt.continuousWithinAt

/-- Exponential damping makes the bounded cosine-tail primitive absolutely
integrable. -/
theorem integrableOn_exp_neg_mul_suzukiCosineTailPartialReal
    {lam : Real} (hlam : 0 < lam) :
    IntegrableOn
      (fun t : Real =>
        Real.exp (-lam * t) * suzukiCosineTailPartialReal t)
      (Ioi 1) := by
  have hexp : IntegrableOn (fun t : Real => Real.exp (-lam * t)) (Ioi 1) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -lam) (neg_lt_zero.mpr hlam) 1)
  apply hexp.mul_bdd (c := 3)
  · exact (continuousOn_suzukiCosineTailPartialReal.mono
      Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using
      abs_suzukiCosineTailPartialReal_le_three ht.le

/-- Integration by parts converts the damped cosine tail into the Abel
average of its bounded primitive. -/
theorem integral_Ioi_exp_neg_mul_cos_div_eq_abelTailAverage
    {lam : Real} (hlam : 0 < lam) :
    (∫ t : Real in Ioi 1,
        Real.exp (-lam * t) * Real.cos t / t) =
      lam * ∫ t : Real in Ioi 1,
        Real.exp (-lam * t) * suzukiCosineTailPartialReal t := by
  let u : Real → Real := fun t => Real.exp (-lam * t)
  let u' : Real → Real := fun t => -lam * Real.exp (-lam * t)
  let v : Real → Real := suzukiCosineTailPartialReal
  let v' : Real → Real := fun t => Real.cos t / t
  have hu : ∀ t ∈ Ioi (1 : Real), HasDerivAt u (u' t) t := by
    intro t ht
    dsimp [u, u']
    have hlinear : HasDerivAt (fun s : Real => -lam * s) (-lam) t := by
      simpa using (hasDerivAt_id t).const_mul (-lam)
    simpa only [mul_comm] using hlinear.exp
  have hv : ∀ t ∈ Ioi (1 : Real), HasDerivAt v (v' t) t := by
    intro t ht
    exact hasDerivAt_suzukiCosineTailPartialReal ht.le
  have huv' : IntegrableOn (u * v') (Ioi (1 : Real)) := by
    change IntegrableOn (fun t : Real => u t * v' t) (Ioi (1 : Real))
    dsimp [u, v']
    simpa only [div_eq_mul_inv, mul_assoc] using
      integrableOn_exp_neg_mul_cos_div_Ioi_one hlam
  have hu'v : IntegrableOn (u' * v) (Ioi (1 : Real)) := by
    have hbase :=
      integrableOn_exp_neg_mul_suzukiCosineTailPartialReal hlam
    have hscaled := hbase.const_mul (-lam)
    change Integrable (fun t : Real => u' t * v t)
      (volume.restrict (Ioi (1 : Real)))
    dsimp [u', v]
    simpa only [mul_assoc] using hscaled
  have hzero : Tendsto (u * v) (𝓝[>] (1 : Real)) (nhds 0) := by
    have huOne : Tendsto u (𝓝[>] (1 : Real))
        (nhds (Real.exp (-lam * 1))) := by
      have hcont : ContinuousAt u 1 := by
        dsimp [u]
        fun_prop
      exact hcont.tendsto.mono_left inf_le_left
    have hvOne : Tendsto v (𝓝[>] (1 : Real)) (nhds 0) := by
      have hcont :=
        (hasDerivAt_suzukiCosineTailPartialReal
          (le_refl (1 : Real))).continuousAt.tendsto
      have hrestricted := hcont.mono_left
        (show 𝓝[>] (1 : Real) ≤ nhds 1 from inf_le_left)
      simpa only [v, suzukiCosineTailPartialReal,
        intervalIntegral.integral_same] using hrestricted
    change Tendsto (fun t : Real => u t * v t)
      (𝓝[>] (1 : Real)) (nhds 0)
    simpa only [mul_zero] using huOne.mul hvOne
  have hinfty : Tendsto (u * v) atTop (nhds 0) := by
    have hscale : Tendsto (fun t : Real => lam * t) atTop atTop :=
      tendsto_id.const_mul_atTop hlam
    have huTop : Tendsto u atTop (nhds 0) := by
      dsimp [u]
      simpa only [Function.comp_def, neg_mul] using
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    have hvTop : Tendsto v atTop (nhds suzukiCosineTailConstant) := by
      exact tendsto_suzukiCosineTailPartialReal
    change Tendsto (fun t : Real => u t * v t) atTop (nhds 0)
    simpa only [zero_mul] using huTop.mul hvTop
  have hparts := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (1 : Real)) (a' := (0 : Real)) (b' := (0 : Real))
    hu hv huv' hu'v hzero hinfty
  have hparts' :
      (∫ t : Real in Ioi 1,
          Real.exp (-lam * t) * Real.cos t / t) =
        -∫ t : Real in Ioi 1,
          (-lam * Real.exp (-lam * t)) *
            suzukiCosineTailPartialReal t := by
    simpa only [u, u', v, v', Pi.mul_apply, div_eq_mul_inv,
      mul_assoc, neg_zero, sub_zero, zero_sub] using hparts
  rw [hparts']
  have hreassociate :
      (fun t : Real =>
        (-lam * Real.exp (-lam * t)) *
          suzukiCosineTailPartialReal t) =
        fun t : Real =>
          -lam * (Real.exp (-lam * t) *
            suzukiCosineTailPartialReal t) := by
    funext t
    ring
  rw [hreassociate, integral_const_mul]
  ring

/-- After the substitution `u = lam * t`, the Abel average is represented on
a fixed ambient measure space by extending it by zero below `lam`. -/
def suzukiAbelTailScaledIntegrand (lam u : Real) : Real :=
  (Ioi lam).indicator
    (fun x : Real =>
      Real.exp (-x) * suzukiCosineTailPartialReal (x / lam)) u

/-- The scaled Abel-tail integrands converge under a fixed integrable
majorant.  This is the continuous analogue of Abel's limit theorem for the
bounded primitive of a conditionally convergent improper integral. -/
theorem tendsto_integral_suzukiAbelTailScaledIntegrand :
    Tendsto
      (fun lam : Real =>
        ∫ u : Real, suzukiAbelTailScaledIntegrand lam u)
      (𝓝[>] (0 : Real)) (nhds suzukiCosineTailConstant) := by
  let majorant : Real → Real :=
    (Ioi (0 : Real)).indicator (fun u : Real => 3 * Real.exp (-u))
  have hmajorant : Integrable majorant volume := by
    have hexp :
        IntegrableOn (fun u : Real => Real.exp (-u)) (Ioi 0) := by
      simpa only [neg_one_mul] using
        (integrableOn_exp_mul_Ioi (a := (-1 : Real)) (by norm_num) 0)
    have hscaled := hexp.const_mul 3
    unfold majorant
    rw [integrable_indicator_iff measurableSet_Ioi]
    change Integrable (fun u : Real => 3 * Real.exp (-u))
      (volume.restrict (Ioi (0 : Real)))
    exact hscaled
  have hmeas :
      ∀ᶠ lam : Real in 𝓝[>] 0,
        AEStronglyMeasurable
          (suzukiAbelTailScaledIntegrand lam) volume := by
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    unfold suzukiAbelTailScaledIntegrand
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    have hquot : ContinuousOn (fun u : Real => u / lam) (Ioi lam) := by
      fun_prop
    have hmaps : MapsTo (fun u : Real => u / lam) (Ioi lam) (Ici 1) := by
      intro u hu
      exact mem_Ici.mpr ((le_div_iff₀ hlam).2 (by simpa using hu.le))
    have htail : ContinuousOn
        (fun u : Real => suzukiCosineTailPartialReal (u / lam))
        (Ioi lam) :=
      continuousOn_suzukiCosineTailPartialReal.comp hquot hmaps
    have hproduct : ContinuousOn
        (fun u : Real =>
          Real.exp (-u) * suzukiCosineTailPartialReal (u / lam))
        (Ioi lam) := by
      apply ContinuousOn.mul
      · fun_prop
      · exact htail
    exact hproduct.aestronglyMeasurable measurableSet_Ioi
  have hbound :
      ∀ᶠ lam : Real in 𝓝[>] 0,
        ∀ᵐ u : Real ∂volume,
          ‖suzukiAbelTailScaledIntegrand lam u‖ ≤ majorant u := by
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact Eventually.of_forall (fun u => by
      change ‖suzukiAbelTailScaledIntegrand lam u‖ ≤
        (Ioi (0 : Real)).indicator
          (fun x : Real => 3 * Real.exp (-x)) u
      by_cases hu : u ∈ Ioi (0 : Real)
      · by_cases hlamu : u ∈ Ioi lam
        · have hratio : 1 ≤ u / lam :=
            (le_div_iff₀ hlam).2 (by simpa using hlamu.le)
          have htailBound :=
            abs_suzukiCosineTailPartialReal_le_three hratio
          rw [suzukiAbelTailScaledIntegrand,
            indicator_of_mem hlamu, indicator_of_mem hu,
            Real.norm_eq_abs, abs_mul,
            abs_of_pos (Real.exp_pos (-u))]
          calc
            Real.exp (-u) * abs (suzukiCosineTailPartialReal (u / lam)) ≤
                Real.exp (-u) * 3 :=
              mul_le_mul_of_nonneg_left htailBound (Real.exp_pos (-u)).le
            _ = 3 * Real.exp (-u) := mul_comm _ _
        · rw [suzukiAbelTailScaledIntegrand,
            indicator_of_notMem hlamu, norm_zero,
            indicator_of_mem hu]
          positivity
      · have huNonpos : u ≤ 0 := not_lt.mp hu
        have hnot : u ∉ Ioi lam := by
          intro hmem
          linarith [mem_Ioi.mp hlam, mem_Ioi.mp hmem]
        simp only [suzukiAbelTailScaledIntegrand,
          indicator_of_notMem hnot, norm_zero,
          indicator_of_notMem hu, le_refl])
  have hlimit :
      ∀ᵐ u : Real ∂volume,
        Tendsto
          (fun lam : Real => suzukiAbelTailScaledIntegrand lam u)
          (𝓝[>] (0 : Real))
          (nhds ((Ioi (0 : Real)).indicator
            (fun x : Real =>
              Real.exp (-x) * suzukiCosineTailConstant) u)) := by
    exact Eventually.of_forall (fun u => by
      by_cases hu : u ∈ Ioi (0 : Real)
      · have hquot : Tendsto (fun lam : Real => u / lam)
            (𝓝[>] (0 : Real)) atTop := by
          have hinv : Tendsto (fun lam : Real => lam⁻¹)
              (𝓝[>] (0 : Real)) atTop := tendsto_inv_nhdsGT_zero
          have hmul : Tendsto (fun lam : Real => u * lam⁻¹)
              (𝓝[>] (0 : Real)) atTop :=
            Filter.Tendsto.pos_mul_atTop (mem_Ioi.mp hu)
              tendsto_const_nhds hinv
          simpa only [div_eq_mul_inv] using hmul
        have htail := tendsto_suzukiCosineTailPartialReal.comp hquot
        have hconst : Tendsto
            (fun _lam : Real => Real.exp (-u))
            (𝓝[>] (0 : Real)) (nhds (Real.exp (-u))) :=
          tendsto_const_nhds
        have hweighted : Tendsto
            (fun lam : Real =>
              Real.exp (-u) *
                suzukiCosineTailPartialReal (u / lam))
            (𝓝[>] (0 : Real))
            (nhds (Real.exp (-u) * suzukiCosineTailConstant)) := by
          simpa only [Function.comp_apply] using hconst.mul htail
        have hevent :
            (fun lam : Real => suzukiAbelTailScaledIntegrand lam u) =ᶠ[
              𝓝[>] (0 : Real)]
              (fun lam : Real =>
                Real.exp (-u) *
                  suzukiCosineTailPartialReal (u / lam)) := by
          filter_upwards [mem_nhdsWithin_of_mem_nhds
            (Iio_mem_nhds (mem_Ioi.mp hu))] with lam hlamu
          rw [suzukiAbelTailScaledIntegrand,
            indicator_of_mem (mem_Ioi.mpr hlamu)]
        simpa only [indicator_of_mem hu] using hweighted.congr' hevent.symm
      · have huNonpos : u ≤ 0 := not_lt.mp hu
        have hzero : Tendsto (fun _lam : Real => (0 : Real))
            (𝓝[>] (0 : Real)) (nhds 0) := tendsto_const_nhds
        have hevent :
            (fun lam : Real => suzukiAbelTailScaledIntegrand lam u) =ᶠ[
              𝓝[>] (0 : Real)] (fun _lam : Real => 0) := by
          filter_upwards [self_mem_nhdsWithin] with lam hlam
          have hnot : u ∉ Ioi lam := by
            intro hmem
            linarith [mem_Ioi.mp hlam, mem_Ioi.mp hmem]
          rw [suzukiAbelTailScaledIntegrand,
            indicator_of_notMem hnot]
        simpa only [indicator_of_notMem hu] using hzero.congr' hevent.symm)
  have hdct := tendsto_integral_filter_of_dominated_convergence
    majorant hmeas hbound hmajorant hlimit
  have hvalue :
      (∫ u : Real,
        (Ioi (0 : Real)).indicator
          (fun x : Real =>
            Real.exp (-x) * suzukiCosineTailConstant) u) =
        suzukiCosineTailConstant := by
    rw [integral_indicator measurableSet_Ioi, integral_mul_const,
      integral_exp_neg_Ioi_zero, one_mul]
  rw [hvalue] at hdct
  exact hdct

/-- The fixed-domain scaled integral is exactly the Abel average of the
cosine-tail primitive. -/
theorem integral_suzukiAbelTailScaledIntegrand_eq_abelTailAverage
    {lam : Real} (hlam : 0 < lam) :
    (∫ u : Real, suzukiAbelTailScaledIntegrand lam u) =
      lam * ∫ t : Real in Ioi 1,
        Real.exp (-lam * t) * suzukiCosineTailPartialReal t := by
  unfold suzukiAbelTailScaledIntegrand
  rw [integral_indicator measurableSet_Ioi]
  have hscale := integral_comp_mul_left_Ioi
    (fun u : Real =>
      Real.exp (-u) * suzukiCosineTailPartialReal (u / lam))
    (1 : Real) hlam
  have hscale' :
      (∫ t : Real in Ioi 1,
          Real.exp (-lam * t) * suzukiCosineTailPartialReal t) =
        lam⁻¹ * ∫ u : Real in Ioi lam,
          Real.exp (-u) * suzukiCosineTailPartialReal (u / lam) := by
    simpa only [mul_one, smul_eq_mul, neg_mul,
      mul_div_cancel_left₀ _ hlam.ne'] using hscale
  have hmultiplied := congrArg (fun x : Real => lam * x) hscale'
  have hnormalized :
      lam *
          (∫ t : Real in Ioi 1,
            Real.exp (-lam * t) * suzukiCosineTailPartialReal t) =
        ∫ u : Real in Ioi lam,
          Real.exp (-u) * suzukiCosineTailPartialReal (u / lam) := by
    calc
      lam *
          (∫ t : Real in Ioi 1,
            Real.exp (-lam * t) * suzukiCosineTailPartialReal t) =
          lam * (lam⁻¹ * ∫ u : Real in Ioi lam,
            Real.exp (-u) * suzukiCosineTailPartialReal (u / lam)) :=
        hmultiplied
      _ = ∫ u : Real in Ioi lam,
          Real.exp (-u) * suzukiCosineTailPartialReal (u / lam) := by
        field_simp [hlam.ne']
  exact hnormalized.symm

/-- The damped cosine tail converges to the independently constructed
oscillatory improper-integral constant as the damping is removed. -/
theorem tendsto_suzukiAbelCosineTailIntegral :
    Tendsto
      (fun lam : Real =>
        ∫ t : Real in Ioi 1,
          Real.exp (-lam * t) * Real.cos t / t)
      (𝓝[>] (0 : Real)) (nhds suzukiCosineTailConstant) := by
  apply tendsto_integral_suzukiAbelTailScaledIntegrand.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  rw [integral_suzukiAbelTailScaledIntegrand_eq_abelTailAverage hlam,
    ← integral_Ioi_exp_neg_mul_cos_div_eq_abelTailAverage hlam]

/-- Removing Abel damping recovers the sum of the regular and oscillatory
constants used by the cutoff construction. -/
theorem tendsto_suzukiAbelCosineNormalizedConstant_to_cutoffConstant :
    Tendsto suzukiAbelCosineNormalizedConstant
      (𝓝[>] (0 : Real))
      (nhds (suzukiCosineRegularConstant + suzukiCosineTailConstant)) := by
  have hsum := tendsto_suzukiAbelCosineRegularIntegral.add
    tendsto_suzukiAbelCosineTailIntegral
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  exact (suzukiAbelCosineNormalizedConstant_eq_regular_add_tail hlam).symm

/-- The exact damped formula converges to minus Euler's constant when the
damping parameter tends to zero from the right. -/
theorem tendsto_suzukiAbelCosineNormalizedConstant_to_neg_euler :
    Tendsto suzukiAbelCosineNormalizedConstant
      (𝓝[>] (0 : Real)) (nhds (-Real.eulerMascheroniConstant)) := by
  have hcontinuous : ContinuousAt
      (fun lam : Real =>
        -Real.eulerMascheroniConstant -
          (1 / 2) * Real.log (lam ^ 2 + 1)) 0 := by
    have harg : ContinuousAt (fun lam : Real => lam ^ 2 + 1) 0 := by
      fun_prop
    have hlog : ContinuousAt
        (fun lam : Real => Real.log (lam ^ 2 + 1)) 0 := by
      have hcomp := (Real.continuousAt_log
        (x := (1 : Real)) one_ne_zero).comp_of_eq harg (by norm_num)
      simpa only [Function.comp_def] using hcomp
    exact continuousAt_const.sub (continuousAt_const.mul hlog)
  have hclosed : Tendsto
      (fun lam : Real =>
        -Real.eulerMascheroniConstant -
          (1 / 2) * Real.log (lam ^ 2 + 1))
      (𝓝[>] (0 : Real)) (nhds (-Real.eulerMascheroniConstant)) := by
    convert hcontinuous.tendsto.mono_left
      (show 𝓝[>] (0 : Real) ≤ nhds 0 from inf_le_left) using 1 <;>
      norm_num [Real.log_one]
  apply hclosed.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  exact (suzukiAbelCosineNormalizedConstant_eq hlam).symm

/-- The cosine-integral constant required by the Suzuki singular-multiplier
calculation, now obtained by uniqueness of the Abel limit. -/
theorem suzukiCosineIntegralConstantIdentity :
    SuzukiCosineIntegralConstantIdentity := by
  change suzukiCosineRegularConstant + suzukiCosineTailConstant =
    -Real.eulerMascheroniConstant
  exact tendsto_nhds_unique
    tendsto_suzukiAbelCosineNormalizedConstant_to_cutoffConstant
    tendsto_suzukiAbelCosineNormalizedConstant_to_neg_euler

end

end M100
end Experiments
end RiemannHypothesisProject
