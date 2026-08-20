import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaFourierDecaySummability

/-!
# M100-DF6F smooth-core Fourier decay at zeta-zero coordinates

This module proves the analytic estimate isolated by the preceding
decay-to-summability reduction. Compact support controls the Fourier--Laplace
exponential on the critical strip, and one integration by parts supplies the
inverse ordinate factor.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open SchwartzLineTestFunction

open scoped ComplexConjugate

/-- A compactly supported Schwartz function remains integrable after
multiplication by a fixed Fourier--Laplace exponential. -/
private theorem integrable_suzukiFourierIntegrand_of_support_subset_Icc
    {a : Real} {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a) (z : Complex) :
    Integrable (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * w x) := by
  have hsub : Function.support
      (fun x : Real =>
        Complex.exp ((x : Complex) * Complex.I * z) * w x) ⊆
        Icc (-a) a := by
    intro x hx
    exact hsupport (fun hw => hx (by simp [hw]))
  apply (integrableOn_iff_integrable_of_support_subset hsub).mp
  exact (by fun_prop : Continuous (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * w x)).continuousOn
    |>.integrableOn_compact isCompact_Icc

/-- On a horizontal strip, the Fourier--Laplace exponential is uniformly
bounded on a fixed compact interval. -/
private theorem norm_suzukiFourierIntegrand_le_exp_radius_mul
    {a : Real} (ha : 0 ≤ a) {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a)
    {z : Complex} (hz : |z.im| ≤ 1) (x : Real) :
    ‖Complex.exp ((x : Complex) * Complex.I * z) * w x‖ ≤
      Real.exp a * ‖w x‖ := by
  by_cases hw : w x = 0
  · simp [hw]
  have hx := hsupport hw
  have hxabs : |x| ≤ a := (abs_le).2 hx
  have hprod : |x * z.im| ≤ a := by
    rw [abs_mul]
    calc
      |x| * |z.im| ≤ a * 1 :=
        mul_le_mul hxabs hz (abs_nonneg _) ha
      _ = a := mul_one a
  have hre : (((x : Complex) * Complex.I * z).re) = -x * z.im := by
    simp
  rw [norm_mul, Complex.norm_exp, hre]
  gcongr
  simpa only [neg_mul] using (neg_le_abs (x * z.im)).trans hprod

/-- The derivative of a smooth-core vector is supported in the closure of the
same compact interval. -/
private theorem support_smoothCore_deriv_subset_Icc
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCoreLinearSubmodule a) :
    Function.support
        ((SchwartzMap.derivCLM Complex Complex v.1 :
          SchwartzLineTestFunction) : Real → Complex) ⊆
      Icc (-a) a := by
  intro x hx
  have hderiv :
      deriv (v.1 : Real → Complex) =
        ((SchwartzMap.derivCLM Complex Complex v.1 :
          SchwartzLineTestFunction) : Real → Complex) := by
    funext y
    exact (SchwartzMap.derivCLM_apply Complex v.1 y).symm
  have hxderiv :
      x ∈ Function.support (deriv (v.1 : Real → Complex)) := by
    rw [hderiv]
    exact hx
  have hxtsupport : x ∈ tsupport (v.1 : Real → Complex) :=
    support_deriv_subset hxderiv
  have hclosure : tsupport (v.1 : Real → Complex) ⊆ Icc (-a) a := by
    change closure (Function.support (v.1 : Real → Complex)) ⊆ Icc (-a) a
    rw [← closure_Ioo (by linarith : -a ≠ a)]
    exact closure_mono v.2
  exact hclosure hxtsupport

/-- The direct compact-support bound for the Fourier--Laplace transform on the
horizontal strip `|Im z| ≤ 1`. -/
theorem norm_suzukiFourierSource_le_exp_radius_mul_integral_norm
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCoreLinearSubmodule a)
    {z : Complex} (hz : |z.im| ≤ 1) :
    ‖suzukiFourierSource v.1 z‖ ≤
      Real.exp a * ∫ x : Real, ‖v.1 x‖ := by
  have hsupport : Function.support v.1 ⊆ Icc (-a) a :=
    v.2.trans Ioo_subset_Icc_self
  have hintegrable :=
    integrable_suzukiFourierIntegrand_of_support_subset_Icc hsupport z
  rw [suzukiFourierSource]
  calc
    ‖∫ x : Real,
        Complex.exp ((x : Complex) * Complex.I * z) * v.1 x‖ ≤
        ∫ x : Real,
          ‖Complex.exp ((x : Complex) * Complex.I * z) * v.1 x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : Real, Real.exp a * ‖v.1 x‖ := by
      apply integral_mono hintegrable.norm
        (v.1.integrable.norm.const_mul (Real.exp a))
      intro x
      exact norm_suzukiFourierIntegrand_le_exp_radius_mul
        ha.le hsupport hz x
    _ = Real.exp a * ∫ x : Real, ‖v.1 x‖ := by
      rw [integral_const_mul]

/-- One integration by parts gives the high-frequency Fourier--Laplace bound
without division, so the statement remains meaningful at `z = 0`. -/
theorem norm_mul_norm_suzukiFourierSource_le_exp_radius_mul_integral_norm_deriv
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCoreLinearSubmodule a)
    {z : Complex} (hz : |z.im| ≤ 1) :
    ‖z‖ * ‖suzukiFourierSource v.1 z‖ ≤
      Real.exp a * ∫ x : Real,
        ‖(SchwartzMap.derivCLM Complex Complex v.1 :
          SchwartzLineTestFunction) x‖ := by
  let dv : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex v.1
  let u : Real → Complex := fun x =>
    Complex.exp ((x : Complex) * Complex.I * z)
  let u' : Real → Complex := fun x =>
    u x * (Complex.I * z)
  have hsupport : Function.support v.1 ⊆ Icc (-a) a :=
    v.2.trans Ioo_subset_Icc_self
  have hdvSupport : Function.support dv ⊆ Icc (-a) a :=
    support_smoothCore_deriv_subset_Icc ha v
  have huv : Integrable (fun x : Real => u x * v.1 x) := by
    simpa only [u] using
      integrable_suzukiFourierIntegrand_of_support_subset_Icc hsupport z
  have huv' : Integrable (fun x : Real => u x * dv x) := by
    simpa only [u] using
      integrable_suzukiFourierIntegrand_of_support_subset_Icc hdvSupport z
  have hu'v : Integrable (fun x : Real => u' x * v.1 x) := by
    have hscaled := huv.const_mul (Complex.I * z)
    exact hscaled.congr (ae_of_all _ fun x => by
      dsimp only [u']
      ring)
  have huDeriv (x : Real) : HasDerivAt u (u' x) x := by
    have hlinear : HasDerivAt
        (fun y : Real => (y : Complex) * Complex.I * z)
        (Complex.I * z) x := by
      have hbase : HasDerivAt
          (fun y : Real => (Complex.I * z) * (y : Complex))
          (Complex.I * z) x := by
        simpa using ((((hasDerivAt_id (x : Complex)).const_mul
          (Complex.I * z)).comp_ofReal))
      have heq :
          (fun y : Real => (y : Complex) * Complex.I * z) =
            fun y : Real => (Complex.I * z) * (y : Complex) := by
        funext y
        ring
      rw [heq]
      exact hbase
    simpa only [u, u'] using hlinear.cexp
  have hvDeriv (x : Real) :
      HasDerivAt (fun y : Real => v.1 y) (dv x) x := by
    simpa only [dv, SchwartzMap.derivCLM_apply] using v.1.hasDerivAt x
  have huv'Pi : Integrable (u * fun x : Real => dv x) := by
    change Integrable (fun x : Real => u x * dv x)
    exact huv'
  have hu'vPi : Integrable (u' * fun x : Real => v.1 x) := by
    change Integrable (fun x : Real => u' x * v.1 x)
    exact hu'v
  have huvPi : Integrable (u * fun x : Real => v.1 x) := by
    change Integrable (fun x : Real => u x * v.1 x)
    exact huv
  have hparts :=
    MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := u) (v := fun x : Real => v.1 x)
      (u' := u') (v' := fun x : Real => dv x)
      (fun x _ => huDeriv x) (fun x _ => hvDeriv x)
      huv'Pi hu'vPi huvPi
  have hfactor :
      (∫ x : Real, u' x * v.1 x) =
        (Complex.I * z) * suzukiFourierSource v.1 z := by
    rw [suzukiFourierSource, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [u', u]
    ring
  have hidentity :
      (∫ x : Real, u x * dv x) =
        -((Complex.I * z) * suzukiFourierSource v.1 z) := by
    simpa only [Pi.mul_apply, hfactor] using hparts
  calc
    ‖z‖ * ‖suzukiFourierSource v.1 z‖ =
        ‖(Complex.I * z) * suzukiFourierSource v.1 z‖ := by simp
    _ = ‖∫ x : Real, u x * dv x‖ := by rw [hidentity, norm_neg]
    _ ≤ ∫ x : Real, ‖u x * dv x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : Real, Real.exp a * ‖dv x‖ := by
      apply integral_mono huv'.norm
        (dv.integrable.norm.const_mul (Real.exp a))
      intro x
      exact norm_suzukiFourierIntegrand_le_exp_radius_mul
        ha.le hdvSupport hz x
    _ = Real.exp a * ∫ x : Real, ‖dv x‖ := by
      rw [integral_const_mul]

/-- Positive-ordinate nontrivial zeta zeroes lie strictly inside the critical
strip. The lower bound follows by applying the known right-half-plane theorem
to the functional reflection. -/
private theorem positiveOrdinateZetaZero_re_pos
    (rho : ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype) :
    0 < (rho : Complex).re := by
  have hreflected :=
    (ComplexCompactExhaustion.positiveOrdinateZetaZero_isNontrivial
      (ComplexCompactExhaustion.positiveOrdinateZetaZeroFunctionalReflection
        rho)).re_lt_one
  rw [ComplexCompactExhaustion.positiveOrdinateZetaZeroFunctionalReflection_value]
    at hreflected
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hreflected
  linarith

/-- The imaginary part of either Suzuki zero coordinate stays in the fixed
horizontal strip required by the compact-support estimate. -/
private theorem abs_im_suzukiSourceGammaArgument_le_one
    (rho : ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype) :
    |(suzukiSourceGammaArgument (rho : Complex)).im| ≤ 1 := by
  have hrePos := positiveOrdinateZetaZero_re_pos rho
  have hreLt :=
    (ComplexCompactExhaustion.positiveOrdinateZetaZero_isNontrivial rho).re_lt_one
  have hhalf : ((1 / 2 : Complex).re) = (1 / 2 : Real) := by norm_num
  rw [suzukiSourceGammaArgument_eq]
  simp only [Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im, one_mul,
    Complex.sub_re, hhalf]
  rw [abs_le]
  constructor <;> linarith

private theorem abs_im_suzukiSourceGammaArgument_conj_le_one
    (rho : ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype) :
    |(suzukiSourceGammaArgument (conj (rho : Complex))).im| ≤ 1 := by
  have hrePos := positiveOrdinateZetaZero_re_pos rho
  have hreLt :=
    (ComplexCompactExhaustion.positiveOrdinateZetaZero_isNontrivial rho).re_lt_one
  have hhalf : ((1 / 2 : Complex).re) = (1 / 2 : Real) := by norm_num
  rw [suzukiSourceGammaArgument_eq]
  simp only [Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im, one_mul,
    Complex.sub_re, Complex.conj_re, hhalf]
  rw [abs_le]
  constructor <;> linarith

/-- The positive ordinate is bounded by the norm of the first Suzuki zero
coordinate. -/
private theorem positiveOrdinate_le_norm_suzukiSourceGammaArgument
    (rho : ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype) :
    (rho : Complex).im ≤
      ‖suzukiSourceGammaArgument (rho : Complex)‖ := by
  calc
    (rho : Complex).im = |-((rho : Complex).im)| := by
      rw [abs_neg, abs_of_pos rho.2]
    _ = |(suzukiSourceGammaArgument (rho : Complex)).re| := by
      rw [suzukiSourceGammaArgument_eq]
      simp
    _ ≤ ‖suzukiSourceGammaArgument (rho : Complex)‖ :=
      Complex.abs_re_le_norm _

/-- The same ordinate bound holds at the conjugate Suzuki zero coordinate. -/
private theorem positiveOrdinate_le_norm_suzukiSourceGammaArgument_conj
    (rho : ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype) :
    (rho : Complex).im ≤
      ‖suzukiSourceGammaArgument (conj (rho : Complex))‖ := by
  calc
    (rho : Complex).im =
        |(suzukiSourceGammaArgument (conj (rho : Complex))).re| := by
      rw [suzukiSourceGammaArgument_eq]
      simp [abs_of_pos rho.2]
    _ ≤ ‖suzukiSourceGammaArgument (conj (rho : Complex))‖ :=
      Complex.abs_re_le_norm _

/-- Compact support and one integration by parts prove the exact one-input
linear zero-coordinate decay proposition required by the DF6F formula chain. -/
theorem suzukiSourceAaSmoothCoreFourierLinearZeroDecay_proved :
    SuzukiSourceAaSmoothCoreFourierLinearZeroDecay := by
  intro v
  let dv : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex v.1
  let C : Real := Real.exp suzukiProjectAStar *
    ((∫ x : Real, ‖v.1 x‖) + ∫ x : Real, ‖dv x‖)
  have hnormV : 0 ≤ ∫ x : Real, ‖v.1 x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hnormDv : 0 ≤ ∫ x : Real, ‖dv x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro rho
  have hbound (z : Complex) (hzstrip : |z.im| ≤ 1)
      (hheight : (rho : Complex).im ≤ ‖z‖) :
      ‖suzukiFourierSource v.1 z‖ ≤
        C / ComplexCompactExhaustion.positiveOrdinateZetaZeroClampedHeight rho := by
    rw [ComplexCompactExhaustion.positiveOrdinateZetaZeroClampedHeight]
    by_cases hlow : (rho : Complex).im ≤ 1
    · rw [max_eq_left hlow, div_one]
      exact (norm_suzukiFourierSource_le_exp_radius_mul_integral_norm
        suzukiProjectAStar_pos v hzstrip).trans (by
          dsimp only [C]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnormDv)
            (Real.exp_pos _).le)
    · have hhigh : 1 ≤ (rho : Complex).im := (lt_of_not_ge hlow).le
      rw [max_eq_right hhigh, le_div_iff₀ rho.2]
      calc
        ‖suzukiFourierSource v.1 z‖ * (rho : Complex).im ≤
            ‖suzukiFourierSource v.1 z‖ * ‖z‖ :=
          mul_le_mul_of_nonneg_left hheight (norm_nonneg _)
        _ = ‖z‖ * ‖suzukiFourierSource v.1 z‖ := mul_comm _ _
        _ ≤ Real.exp suzukiProjectAStar * ∫ x : Real, ‖dv x‖ := by
          simpa only [dv] using
            norm_mul_norm_suzukiFourierSource_le_exp_radius_mul_integral_norm_deriv
              suzukiProjectAStar_pos v hzstrip
        _ ≤ C := by
          dsimp only [C]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hnormV)
            (Real.exp_pos _).le
  exact ⟨
    hbound (suzukiSourceGammaArgument (rho : Complex))
      (abs_im_suzukiSourceGammaArgument_le_one rho)
      (positiveOrdinate_le_norm_suzukiSourceGammaArgument rho),
    hbound (suzukiSourceGammaArgument (conj (rho : Complex)))
      (abs_im_suzukiSourceGammaArgument_conj_le_one rho)
      (positiveOrdinate_le_norm_suzukiSourceGammaArgument_conj rho)⟩

end

end RiemannHypothesisProject.Experiments.M100
