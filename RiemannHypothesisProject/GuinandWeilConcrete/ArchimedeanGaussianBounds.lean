import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import RiemannHypothesisProject.GuinandWeilConcrete.ArchimedeanLogDerivative
import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianContourShift
import RiemannHypothesisProject.GuinandWeilConcrete.XiContourWeight

/-!
# Gaussian-compatible Archimedean bounds

This module proves unconditional bounds for the Gamma logarithmic derivative
on the fixed strip used by the Guinand-Weil contour.  The proof uses Euler's
Gamma integral for `Gamma` and `Gamma'`, together with Euler reflection for
the reciprocal Gamma factor.  No Binet or Stirling hypothesis is introduced.
-/

namespace RiemannHypothesisProject

open Asymptotics Complex Filter MeasureTheory Set Topology
open scoped Topology

noncomputable section

/-- A two-endpoint majorant for Gamma integrals on a closed real strip. -/
private def gammaStripMajorant (a b x : Real) : Real :=
  Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1))

/-- The analogous majorant for the differentiated Gamma integral. -/
private def gammaDerivativeStripMajorant (a b x : Real) : Real :=
  gammaStripMajorant a b x * abs (Real.log x)

private theorem rpow_le_endpoint_sum
    {a b sigma x : Real} (hx : 0 < x) (hab : a <= sigma) (hsb : sigma <= b) :
    x ^ (sigma - 1) <= x ^ (a - 1) + x ^ (b - 1) := by
  rcases le_total x 1 with hx1 | h1x
  · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h1x (by linarith)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))

private theorem integrableOn_gammaStripMajorant
    {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (gammaStripMajorant a b) (Set.Ioi 0) := by
  have hA := Real.GammaIntegral_convergent ha
  have hB := Real.GammaIntegral_convergent hb
  have hfun : gammaStripMajorant a b =
      (fun x => Real.exp (-x) * x ^ (a - 1)) +
        fun x => Real.exp (-x) * x ^ (b - 1) := by
    funext x
    simp only [gammaStripMajorant, Pi.add_apply]
    ring
  rw [hfun]
  exact hA.add hB

private theorem integrableOn_gammaDerivativeIntegrand
    {s : Complex} (hs : 0 < s.re) :
    IntegrableOn
      (fun x : Real =>
        (x : Complex) ^ (s - 1) *
          ((Real.log x * Real.exp (-x) : Real) : Complex))
      (Set.Ioi 0) := by
  have hlocal : LocallyIntegrableOn
      (fun x : Real => (Real.exp (-x) : Complex)) (Set.Ioi 0) := by
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp continuous_neg)).continuousOn.locallyIntegrableOn
        measurableSet_Ioi
  have htop :
      (fun x : Real => (Real.exp (-x) : Complex)) =O[atTop]
        (fun x : Real => x ^ (-(s.re + 1))) := by
    rw [<- isBigO_norm_left]
    simp_rw [norm_real, isBigO_norm_left]
    simpa only [neg_one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-(s.re + 1))).isBigO
  have hbot :
      (fun x : Real => (Real.exp (-x) : Complex)) =O[nhdsWithin 0 (Set.Ioi 0)]
        (fun x : Real => x ^ (-(0 : Real))) := by
    have htendsto : Tendsto
        (fun x : Real => (Real.exp (-x) : Complex))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have hcont : ContinuousAt
          (fun x : Real => (Real.exp (-x) : Complex)) 0 := by fun_prop
      have hwithin : ContinuousWithinAt
          (fun x : Real => (Real.exp (-x) : Complex)) (Set.Ioi 0) 0 :=
        hcont.continuousWithinAt
      change Tendsto (fun x : Real => (Real.exp (-x) : Complex))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((Real.exp (-0) : Real) : Complex)) at hwithin
      have hzero : (((Real.exp (-0) : Real) : Complex)) = 1 := by norm_num
      rw [hzero] at hwithin
      exact hwithin
    simpa only [neg_zero, Real.rpow_zero] using
      (isBigO_const_of_tendsto htendsto one_ne_zero)
  have hconv :=
    (mellin_hasDerivAt_of_isBigO_rpow
      (f := fun x : Real => (Real.exp (-x) : Complex))
      (s := s) hlocal htop (by linarith) hbot hs).1
  simpa only [MellinConvergent, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_mul, mul_assoc] using hconv

private theorem integrableOn_gammaDerivativeStripMajorant
    {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (gammaDerivativeStripMajorant a b) (Set.Ioi 0) := by
  have hA := (integrableOn_gammaDerivativeIntegrand
    (s := (a : Complex)) (by simpa)).norm
  have hB := (integrableOn_gammaDerivativeIntegrand
    (s := (b : Complex)) (by simpa)).norm
  have hA' : IntegrableOn
      (fun x : Real =>
        Real.exp (-x) * x ^ (a - 1) * abs (Real.log x))
      (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun hA ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      Complex.sub_re, Complex.ofReal_re, one_re, norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (Real.exp_pos _), abs_neg]
    ring
  have hB' : IntegrableOn
      (fun x : Real =>
        Real.exp (-x) * x ^ (b - 1) * abs (Real.log x))
      (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun hB ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      Complex.sub_re, Complex.ofReal_re, one_re, norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (Real.exp_pos _), abs_neg]
    ring
  have hfun : gammaDerivativeStripMajorant a b =
      (fun x => Real.exp (-x) * x ^ (a - 1) * abs (Real.log x)) +
        fun x => Real.exp (-x) * x ^ (b - 1) * abs (Real.log x) := by
    funext x
    simp only [gammaDerivativeStripMajorant, gammaStripMajorant, Pi.add_apply]
    ring
  rw [hfun]
  exact hA'.add hB'

private theorem norm_Gamma_le_gammaStripMajorant_integral
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    {s : Complex} (has : a <= s.re) (hsb : s.re <= b) :
    norm (Complex.Gamma s) <=
      MeasureTheory.integral (volume.restrict (Set.Ioi 0))
        (gammaStripMajorant a b) := by
  rw [Complex.Gamma_eq_integral (ha.trans_le has)]
  apply MeasureTheory.norm_integral_le_of_norm_le
    (integrableOn_gammaStripMajorant ha hb)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := hx
  simp only [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
    Complex.sub_re, one_re]
  dsimp only [gammaStripMajorant]
  exact mul_le_mul_of_nonneg_left
    (rpow_le_endpoint_sum hxpos has hsb) (Real.exp_pos _).le

private theorem norm_deriv_Gamma_le_gammaDerivativeStripMajorant_integral
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    {s : Complex} (has : a <= s.re) (hsb : s.re <= b) :
    norm (deriv Complex.Gamma s) <=
      MeasureTheory.integral (volume.restrict (Set.Ioi 0))
        (gammaDerivativeStripMajorant a b) := by
  have hderiv := (Complex.hasDerivAt_GammaIntegral (ha.trans_le has)).deriv
  have hopen : IsOpen {z : Complex | 0 < z.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  have heq : Complex.Gamma =ᶠ[nhds s] Complex.GammaIntegral := by
    filter_upwards [hopen.mem_nhds (ha.trans_le has)] with z hz
    exact Complex.Gamma_eq_integral hz
  rw [heq.deriv_eq]
  rw [hderiv]
  apply MeasureTheory.norm_integral_le_of_norm_le
    (integrableOn_gammaDerivativeStripMajorant ha hb)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := hx
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
    Complex.sub_re, one_re, norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_neg]
  dsimp only [gammaDerivativeStripMajorant, gammaStripMajorant]
  have hpow := rpow_le_endpoint_sum hxpos has hsb
  calc
    x ^ (s.re - 1) * (abs (Real.log x) * Real.exp (-x)) =
        Real.exp (-x) * x ^ (s.re - 1) * abs (Real.log x) := by ring
    _ <= Real.exp (-x) *
        (x ^ (a - 1) + x ^ (b - 1)) * abs (Real.log x) := by
      gcongr

private theorem norm_complex_sin_le_exp_norm (z : Complex) :
    norm (Complex.sin z) <= Real.exp (norm z) := by
  change norm ((Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) *
      Complex.I / 2) <= Real.exp (norm z)
  rw [norm_div, norm_mul, norm_I, norm_ofNat, mul_one]
  calc
    norm (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) / 2 <=
        (norm (Complex.exp (-z * Complex.I)) +
          norm (Complex.exp (z * Complex.I))) / 2 := by
      gcongr
      exact norm_sub_le _ _
    _ <= (Real.exp (norm (-z * Complex.I)) +
          Real.exp (norm (z * Complex.I))) / 2 := by
      gcongr <;> exact Complex.norm_exp_le_exp_norm _
    _ = Real.exp (norm z) := by simp

private theorem inv_Gamma_eq_reflected_mul_sin_div_pi
    {s : Complex} (hs : 0 < s.re) (hones : 0 < (1 - s).re) :
    (Complex.Gamma s)⁻¹ =
      Complex.Gamma (1 - s) * Complex.sin ((Real.pi : Complex) * s) /
        (Real.pi : Complex) := by
  have hgamma : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hgammaOne : Complex.Gamma (1 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hones
  have hpi : (Real.pi : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hreflect := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin ((Real.pi : Complex) * s) ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at hreflect
    exact (mul_ne_zero hgamma hgammaOne) hreflect
  have hprod : Complex.Gamma s *
      (Complex.Gamma (1 - s) *
        Complex.sin ((Real.pi : Complex) * s) / (Real.pi : Complex)) = 1 := by
    calc
      Complex.Gamma s *
          (Complex.Gamma (1 - s) *
            Complex.sin ((Real.pi : Complex) * s) / (Real.pi : Complex)) =
        (Complex.Gamma s * Complex.Gamma (1 - s)) *
          Complex.sin ((Real.pi : Complex) * s) / (Real.pi : Complex) := by ring
      _ = ((Real.pi : Complex) /
          Complex.sin ((Real.pi : Complex) * s)) *
          Complex.sin ((Real.pi : Complex) * s) / (Real.pi : Complex) := by
        rw [hreflect]
      _ = 1 := by field_simp [hsin, hpi]
  exact inv_eq_of_mul_eq_one_right hprod

/-- The reciprocal Gamma function has a uniform exponential majorant on the
critical half-line.  This is the reflection-formula input needed for lower
bounds on the right-half-plane xi factor. -/
theorem exists_pos_const_norm_Gamma_inv_halfLine_le_exp :
    exists C : Real, 0 < C /\
      forall t : Real,
        norm (Complex.Gamma
          ((1 / 2 : Complex) + (t : Complex) * Complex.I))⁻¹ <=
          C * Real.exp (Real.pi * (abs t + 1)) := by
  let G : Real := MeasureTheory.integral (volume.restrict (Set.Ioi 0))
    (gammaStripMajorant (1 / 2 : Real) (1 / 2 : Real))
  have hGnonneg : 0 <= G := by
    apply integral_nonneg_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [G, gammaStripMajorant]
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _))
  let C : Real := (G + 1) / Real.pi
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t
  let s : Complex := (1 / 2 : Complex) + (t : Complex) * Complex.I
  have hsre : s.re = 1 / 2 := by simp [s]
  have hspos : 0 < s.re := by rw [hsre]; norm_num
  have honespos : 0 < (1 - s).re := by
    simp only [Complex.sub_re, one_re, hsre]
    norm_num
  have hgammaOne : norm (Complex.Gamma (1 - s)) <= G := by
    have hlower : (1 / 2 : Real) <= (1 - s).re := by
      simp only [Complex.sub_re, one_re, hsre]
      norm_num
    have hupper : (1 - s).re <= (1 / 2 : Real) := by
      simp only [Complex.sub_re, one_re, hsre]
      norm_num
    simpa only [G] using
      norm_Gamma_le_gammaStripMajorant_integral
        (a := (1 / 2 : Real)) (b := (1 / 2 : Real))
        (by norm_num) (by norm_num) hlower hupper
  have hs_norm : norm s <= abs t + 1 := by
    calc
      norm s <= norm (1 / 2 : Complex) +
          norm ((t : Complex) * Complex.I) := by
        simpa only [s] using
          norm_add_le (1 / 2 : Complex) ((t : Complex) * Complex.I)
      _ = 1 / 2 + abs t := by simp [Real.norm_eq_abs]
      _ <= abs t + 1 := by linarith
  have hsin : norm (Complex.sin ((Real.pi : Complex) * s)) <=
      Real.exp (Real.pi * (abs t + 1)) := by
    calc
      norm (Complex.sin ((Real.pi : Complex) * s)) <=
          Real.exp (norm ((Real.pi : Complex) * s)) :=
        norm_complex_sin_le_exp_norm _
      _ <= Real.exp (Real.pi * (abs t + 1)) := by
        apply Real.exp_le_exp.mpr
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
        exact mul_le_mul_of_nonneg_left hs_norm Real.pi_pos.le
  rw [show (1 / 2 : Complex) + (t : Complex) * Complex.I = s by rfl,
    inv_Gamma_eq_reflected_mul_sin_div_pi hspos honespos,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hGone : norm (Complex.Gamma (1 - s)) <= G + 1 := by linarith
  calc
    norm (Complex.Gamma (1 - s)) *
          norm (Complex.sin ((Real.pi : Complex) * s)) / Real.pi <=
        (G + 1) * Real.exp (Real.pi * (abs t + 1)) / Real.pi := by
      gcongr
    _ = C * Real.exp (Real.pi * (abs t + 1)) := by
      dsimp only [C]
      ring

/--
The digamma function has at most linear-exponential growth on the exact closed
strip needed after the xi-to-spectral coordinate change.  The constant is
uniform in both the real coordinate and the height.
-/
theorem exists_pos_const_norm_digamma_quarter_fiveEighths_strip_le_exp
    : exists C : Real, 0 < C /\
      forall sigma t : Real,
        (1 / 4 : Real) <= sigma -> sigma <= 5 / 8 ->
          norm (Complex.digamma
            ((sigma : Complex) + (t : Complex) * Complex.I)) <=
            C * Real.exp (Real.pi * (abs t + 1)) := by
  let D : Real := MeasureTheory.integral (volume.restrict (Set.Ioi 0))
    (gammaDerivativeStripMajorant (1 / 4 : Real) (5 / 8 : Real))
  let G : Real := MeasureTheory.integral (volume.restrict (Set.Ioi 0))
    (gammaStripMajorant (3 / 8 : Real) (3 / 4 : Real))
  have hDnonneg : 0 <= D := by
    apply integral_nonneg_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [D, gammaDerivativeStripMajorant, gammaStripMajorant]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le
        (add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _)))
      (abs_nonneg _)
  have hGnonneg : 0 <= G := by
    apply integral_nonneg_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [G, gammaStripMajorant]
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _))
  let C : Real := (D + 1) * (G + 1) / Real.pi
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma hsigmaupper
  let s : Complex := (sigma : Complex) + (t : Complex) * Complex.I
  have hsre : s.re = sigma := by simp [s]
  have hspos : 0 < s.re := by rw [hsre]; linarith
  have honespos : 0 < (1 - s).re := by
    simp only [Complex.sub_re, one_re, hsre]
    linarith
  have hderiv : norm (deriv Complex.Gamma s) <= D := by
    simpa only [D] using
      norm_deriv_Gamma_le_gammaDerivativeStripMajorant_integral
        (a := (1 / 4 : Real)) (b := (5 / 8 : Real))
        (by norm_num) (by norm_num)
        (by rw [hsre]; exact hsigma) (by rw [hsre]; exact hsigmaupper)
  have hgammaOne : norm (Complex.Gamma (1 - s)) <= G := by
    have hlower : (3 / 8 : Real) <= (1 - s).re := by
      simp only [Complex.sub_re, one_re, hsre]
      linarith
    have hupper : (1 - s).re <= (3 / 4 : Real) := by
      simp only [Complex.sub_re, one_re, hsre]
      linarith
    simpa only [G] using
      norm_Gamma_le_gammaStripMajorant_integral
        (a := (3 / 8 : Real)) (b := (3 / 4 : Real))
        (by norm_num) (by norm_num) hlower hupper
  have hs_norm : norm s <= abs t + 1 := by
    calc
      norm s <= norm (sigma : Complex) +
          norm ((t : Complex) * Complex.I) := by
        simpa only [s] using norm_add_le (sigma : Complex) ((t : Complex) * Complex.I)
      _ = abs sigma + abs t := by simp [Real.norm_eq_abs]
      _ <= abs t + 1 := by
        rw [abs_of_nonneg (by linarith : 0 <= sigma)]
        linarith
  have hsin : norm (Complex.sin ((Real.pi : Complex) * s)) <=
      Real.exp (Real.pi * (abs t + 1)) := by
    calc
      norm (Complex.sin ((Real.pi : Complex) * s)) <=
          Real.exp (norm ((Real.pi : Complex) * s)) :=
        norm_complex_sin_le_exp_norm _
      _ <= Real.exp (Real.pi * (abs t + 1)) := by
        apply Real.exp_le_exp.mpr
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
        exact mul_le_mul_of_nonneg_left hs_norm Real.pi_pos.le
  have hinv : norm (Complex.Gamma s)⁻¹ <=
      (G + 1) / Real.pi * Real.exp (Real.pi * (abs t + 1)) := by
    rw [inv_Gamma_eq_reflected_mul_sin_div_pi hspos honespos,
      norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hGone : norm (Complex.Gamma (1 - s)) <= G + 1 := by linarith
    calc
      norm (Complex.Gamma (1 - s)) *
            norm (Complex.sin ((Real.pi : Complex) * s)) / Real.pi <=
          (G + 1) * Real.exp (Real.pi * (abs t + 1)) / Real.pi := by
        gcongr
      _ = (G + 1) / Real.pi *
          Real.exp (Real.pi * (abs t + 1)) := by ring
  rw [Complex.digamma_def, logDeriv_apply, div_eq_mul_inv, norm_mul]
  have hDone : norm (deriv Complex.Gamma s) <= D + 1 := by linarith
  calc
    norm (deriv Complex.Gamma s) * norm (Complex.Gamma s)⁻¹ <=
        (D + 1) *
          ((G + 1) / Real.pi * Real.exp (Real.pi * (abs t + 1))) := by
      exact mul_le_mul hDone hinv (norm_nonneg _) (by positivity)
    _ = C * Real.exp (Real.pi * (abs t + 1)) := by
      dsimp only [C]
      ring

/-- The Gamma-factor logarithmic derivative in the spectral coordinate. -/
noncomputable def guinandWeilXiArchimedeanSpectralFactor
    (z : Complex) : Complex :=
  -(Real.log Real.pi : Complex) / 2 +
    Complex.digamma
      ((1 / 4 : Complex) + Complex.I * z / 2) / 2

/-- A polynomial-Gaussian source times the spectral Gamma factor. -/
noncomputable def guinandWeilXiArchimedeanSpectralIntegrand
    (p : Polynomial Real) (z : Complex) : Complex :=
  guinandWeilPiPolynomialGaussianSource (guinandWeilPiEvenPolynomial p) z *
    guinandWeilXiArchimedeanSpectralFactor z

private theorem analyticAt_digamma_of_re_pos
    {s : Complex} (hs : 0 < s.re) :
    AnalyticAt Complex Complex.digamma s := by
  have hgamma : AnalyticAt Complex Complex.Gamma s :=
    analyticAt_iff_eventually_differentiableAt.mpr (by
      have hopen : IsOpen {z : Complex | 0 < z.re} :=
        continuous_re.isOpen_preimage _ isOpen_Ioi
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact Complex.differentiableAt_Gamma z (fun m h => by
        have hre := congrArg Complex.re h
        simp at hre
        linarith))
  have hgamma_ne : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs
  simpa only [Complex.digamma_def, logDeriv] using
    hgamma.deriv.div hgamma hgamma_ne

private theorem differentiableOn_xiArchimedeanSpectralIntegrand_strip
    (p : Polynomial Real) :
    DifferentiableOn Complex (guinandWeilXiArchimedeanSpectralIntegrand p)
      {z : Complex | -(3 / 4 : Real) <= z.im /\ z.im <= 0} := by
  intro z hz
  rcases hz with ⟨hzLower, hzUpper⟩
  have hw : 0 <
      ((1 / 4 : Complex) + Complex.I * z / 2).re := by
    simp only [Complex.add_re, Complex.div_re, Complex.mul_re, I_re,
      zero_mul, I_im, one_mul]
    norm_num
    linarith
  have hdigamma : DifferentiableAt Complex
      (fun z : Complex => Complex.digamma
        ((1 / 4 : Complex) + Complex.I * z / 2)) z :=
    by
      exact (analyticAt_digamma_of_re_pos hw).differentiableAt.comp z (by fun_prop)
  have hfactor : DifferentiableAt Complex
      guinandWeilXiArchimedeanSpectralFactor z := by
    unfold guinandWeilXiArchimedeanSpectralFactor
    exact (differentiableAt_const _).add
      (hdigamma.div_const 2)
  unfold guinandWeilXiArchimedeanSpectralIntegrand
  exact (((guinandWeilPiEvenPolynomial p).differentiable_aeval.mul
    differentiable_guinandWeilPiGaussianSource).differentiableAt.mul
      hfactor).differentiableWithinAt

private theorem exists_pos_const_norm_xiArchimedeanSpectralFactor_strip_le_exp :
    exists K : Real, 0 < K /\
      forall x y : Real,
        -(3 / 4 : Real) <= y -> y <= 0 ->
          norm (guinandWeilXiArchimedeanSpectralFactor
            ((x : Complex) + (y : Complex) * Complex.I)) <=
            K * Real.exp (Real.pi * (abs x + 1)) := by
  rcases exists_pos_const_norm_digamma_quarter_fiveEighths_strip_le_exp with
    ⟨C, hC, hbound⟩
  let A : Real := norm ((Real.log Real.pi : Complex) / 2)
  let K : Real := A + C / 2 + 1
  have hK : 0 < K := by
    dsimp only [K, A]
    positivity
  refine ⟨K, hK, ?_⟩
  intro x y hyLower hyUpper
  let w : Complex :=
    (1 / 4 : Complex) + Complex.I *
      ((x : Complex) + (y : Complex) * Complex.I) / 2
  have hwre : w.re = 1 / 4 - y / 2 := by
    simp [w]
    ring
  have hwim : w.im = x / 2 := by
    simp [w]
  have hwLower : (1 / 4 : Real) <= w.re := by rw [hwre]; linarith
  have hwUpper : w.re <= (5 / 8 : Real) := by rw [hwre]; linarith
  have hdigamma := hbound w.re w.im hwLower hwUpper
  have hexpMono :
      Real.exp (Real.pi * (abs w.im + 1)) <=
        Real.exp (Real.pi * (abs x + 1)) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    rw [hwim, abs_div]
    norm_num
  have hdigamma' : norm (Complex.digamma w) <=
      C * Real.exp (Real.pi * (abs x + 1)) :=
    by
      have hw_eq : (w.re : Complex) + (w.im : Complex) * Complex.I = w :=
        Complex.re_add_im w
      rw [hw_eq] at hdigamma
      exact hdigamma.trans (mul_le_mul_of_nonneg_left hexpMono hC.le)
  have hexpOne : 1 <= Real.exp (Real.pi * (abs x + 1)) := by
    rw [Real.one_le_exp_iff]
    positivity
  unfold guinandWeilXiArchimedeanSpectralFactor
  change norm (-(Real.log Real.pi : Complex) / 2 + Complex.digamma w / 2) <= _
  have htriangle := norm_add_le
    (-(Real.log Real.pi : Complex) / 2) (Complex.digamma w / 2)
  rw [norm_div, norm_neg, norm_ofNat, norm_div, norm_ofNat] at htriangle
  have hA : norm (Real.log Real.pi : Complex) / 2 <=
      A * Real.exp (Real.pi * (abs x + 1)) := by
    dsimp only [A]
    rw [norm_div, norm_ofNat]
    exact le_mul_of_one_le_right (by positivity) hexpOne
  calc
    norm (-(Real.log Real.pi : Complex) / 2 + Complex.digamma w / 2) <=
        norm (Real.log Real.pi : Complex) / 2 +
          norm (Complex.digamma w) / 2 := htriangle
    _ <= A * Real.exp (Real.pi * (abs x + 1)) +
          C * Real.exp (Real.pi * (abs x + 1)) / 2 := by
      gcongr
    _ <= K * Real.exp (Real.pi * (abs x + 1)) := by
      dsimp only [K]
      nlinarith [Real.exp_pos (Real.pi * (abs x + 1))]

private theorem integrable_abs_add_three_pow_mul_exp_neg_mul_sq
    (n : Nat) {b : Real} (hb : 0 < b) :
    Integrable fun x : Real =>
      (abs x + 3) ^ n * Real.exp (-b * x ^ 2) := by
  have hpowBase :=
    (integrable_rpow_mul_exp_neg_mul_sq hb
      (s := (n : Real))
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))).norm
  have hpow : Integrable fun x : Real =>
      abs x ^ n * Real.exp (-b * x ^ 2) := by
    convert hpowBase using 1
    funext x
    simp only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul,
      abs_pow, abs_abs, abs_of_pos (Real.exp_pos _)]
  have hconstant : Integrable fun x : Real =>
      3 ^ n * Real.exp (-b * x ^ 2) :=
    (integrable_exp_neg_mul_sq hb).const_mul (3 ^ n)
  have hmajor : Integrable fun x : Real =>
      2 ^ (n - 1) *
        (abs x ^ n * Real.exp (-b * x ^ 2) +
          3 ^ n * Real.exp (-b * x ^ 2)) :=
    (hpow.add hconstant).const_mul (2 ^ (n - 1))
  refine hmajor.mono' ?_ (Eventually.of_forall fun x => ?_)
  · fun_prop
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hadd := add_pow_le (abs_nonneg x) (by norm_num : (0 : Real) <= 3) n
    have hexp := (Real.exp_pos (-b * x ^ 2)).le
    calc
      (abs x + 3) ^ n * Real.exp (-b * x ^ 2) <=
          (2 ^ (n - 1) * (abs x ^ n + 3 ^ n)) *
            Real.exp (-b * x ^ 2) :=
        mul_le_mul_of_nonneg_right hadd hexp
      _ = 2 ^ (n - 1) *
          (abs x ^ n * Real.exp (-b * x ^ 2) +
            3 ^ n * Real.exp (-b * x ^ 2)) := by ring

private theorem exists_pos_const_norm_xiArchimedeanSpectralIntegrand_strip_le :
    forall p : Polynomial Real,
      exists A : Real, 0 < A /\
        forall x y : Real,
          -(3 / 4 : Real) <= y -> y <= 0 ->
            norm (guinandWeilXiArchimedeanSpectralIntegrand p
              ((x : Complex) + (y : Complex) * Complex.I)) <=
              A * (abs x + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
                Real.exp (-(Real.pi / 2) * x ^ 2) := by
  intro p
  rcases exists_pos_const_norm_guinandWeilXiContourWeight_horizontal_le p with
    ⟨B, hB, hsourceBound⟩
  rcases exists_pos_const_norm_xiArchimedeanSpectralFactor_strip_le_exp with
    ⟨K, hK, hfactorBound⟩
  let A : Real := B * K * Real.exp (3 * Real.pi / 2)
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro x y hyLower hyUpper
  let sigma : Real := 1 / 2 - y
  have hsigmaLeft : guinandWeilXiContourLeft <= sigma := by
    norm_num [guinandWeilXiContourLeft, sigma]
    linarith
  have hsigmaRight : sigma <= guinandWeilXiContourRight := by
    norm_num [guinandWeilXiContourRight, sigma]
    linarith
  have hsource := hsourceBound sigma x hsigmaLeft hsigmaRight
  have hweight :
      guinandWeilXiContourWeight p
          ((sigma : Complex) + (x : Complex) * Complex.I) =
        guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p)
          ((x : Complex) + (y : Complex) * Complex.I) := by
    unfold guinandWeilXiContourWeight
    rw [guinandWeilXiContourCoordinate_horizontal]
    congr 2
    dsimp only [sigma]
    push_cast
    ring
  rw [hweight] at hsource
  have hfactor := hfactorBound x y hyLower hyUpper
  have habsorb :
      Real.exp (-Real.pi * x ^ 2) *
          Real.exp (Real.pi * (abs x + 1)) <=
        Real.exp (3 * Real.pi / 2) *
          Real.exp (-(Real.pi / 2) * x ^ 2) := by
    rw [<- Real.exp_add, <- Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsquare : 0 <= (Real.pi / 2) * (abs x - 1) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    have habssq : (abs x) ^ 2 = x ^ 2 := sq_abs x
    calc
      -Real.pi * x ^ 2 + Real.pi * (abs x + 1) <=
          -Real.pi * x ^ 2 + Real.pi * (abs x + 1) +
            (Real.pi / 2) * (abs x - 1) ^ 2 :=
        le_add_of_nonneg_right hsquare
      _ = 3 * Real.pi / 2 + -(Real.pi / 2) * x ^ 2 := by
        rw [<- habssq]
        ring
  simp only [guinandWeilXiArchimedeanSpectralIntegrand, norm_mul]
  calc
    norm (guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p)
          ((x : Complex) + (y : Complex) * Complex.I)) *
        norm (guinandWeilXiArchimedeanSpectralFactor
          ((x : Complex) + (y : Complex) * Complex.I)) <=
      (B * (abs x + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
          Real.exp (-Real.pi * x ^ 2)) *
        (K * Real.exp (Real.pi * (abs x + 1))) := by
      exact mul_le_mul hsource hfactor (norm_nonneg _) (by positivity)
    _ = B * K * (abs x + 3) ^
          (guinandWeilPiEvenPolynomial p).natDegree *
        (Real.exp (-Real.pi * x ^ 2) *
          Real.exp (Real.pi * (abs x + 1))) := by ring
    _ <= B * K * (abs x + 3) ^
          (guinandWeilPiEvenPolynomial p).natDegree *
        (Real.exp (3 * Real.pi / 2) *
          Real.exp (-(Real.pi / 2) * x ^ 2)) := by
      exact mul_le_mul_of_nonneg_left habsorb (by positivity)
    _ = A * (abs x + 3) ^
          (guinandWeilPiEvenPolynomial p).natDegree *
        Real.exp (-(Real.pi / 2) * x ^ 2) := by
      dsimp only [A]
      ring

private theorem integrable_xiArchimedeanSpectralIntegrand_horizontalLine
    (p : Polynomial Real) {y : Real}
    (hyLower : -(3 / 4 : Real) <= y) (hyUpper : y <= 0) :
    Integrable fun x : Real =>
      guinandWeilXiArchimedeanSpectralIntegrand p
        ((x : Complex) + (y : Complex) * Complex.I) := by
  rcases exists_pos_const_norm_xiArchimedeanSpectralIntegrand_strip_le p with
    ⟨A, hA, hbound⟩
  have hbase :=
    integrable_abs_add_three_pow_mul_exp_neg_mul_sq
      (guinandWeilPiEvenPolynomial p).natDegree
      (b := Real.pi / 2) (by positivity)
  have hmajor : Integrable fun x : Real =>
      A * ((abs x + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
        Real.exp (-(Real.pi / 2) * x ^ 2)) := hbase.const_mul A
  refine hmajor.mono' ?_ (Eventually.of_forall fun x => ?_)
  · have hdigamma : Continuous fun x : Real =>
        Complex.digamma
          ((1 / 4 : Complex) + Complex.I *
            ((x : Complex) + (y : Complex) * Complex.I) / 2) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hpos : 0 < ((1 / 4 : Complex) + Complex.I *
          ((x : Complex) + (y : Complex) * Complex.I) / 2).re := by
        simp
        linarith
      have hinner : ContinuousAt (fun x : Real =>
          (1 / 4 : Complex) + Complex.I *
            ((x : Complex) + (y : Complex) * Complex.I) / 2) x := by
        fun_prop
      have hout : ContinuousAt Complex.digamma
          ((1 / 4 : Complex) + Complex.I *
            ((x : Complex) + (y : Complex) * Complex.I) / 2) :=
        (analyticAt_digamma_of_re_pos hpos).continuousAt
      exact ContinuousAt.comp'
        (f := fun x : Real =>
          (1 / 4 : Complex) + Complex.I *
            ((x : Complex) + (y : Complex) * Complex.I) / 2)
        (g := Complex.digamma) hout hinner
    have hsource : Continuous fun x : Real =>
        guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p)
          ((x : Complex) + (y : Complex) * Complex.I) :=
      ((guinandWeilPiEvenPolynomial p).differentiable_aeval.mul
        differentiable_guinandWeilPiGaussianSource).continuous.comp (by fun_prop)
    unfold guinandWeilXiArchimedeanSpectralIntegrand
      guinandWeilXiArchimedeanSpectralFactor
    exact (hsource.mul
      (continuous_const.add (hdigamma.div_const 2))).aestronglyMeasurable
  · have h := hbound x y hyLower hyUpper
    simpa only [Real.norm_eq_abs, abs_of_pos hA, mul_assoc] using h

private theorem tendsto_abs_add_three_pow_mul_exp_neg_mul_sq_cocompact
    (n : Nat) {b : Real} (hb : 0 < b) :
    Tendsto
      (fun x : Real => (abs x + 3) ^ n * Real.exp (-b * x ^ 2))
      (cocompact Real) (nhds 0) := by
  have hpowBase :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (n : Real)
  have hpow : Tendsto
      (fun x : Real => abs x ^ n * Real.exp (-b * x ^ 2))
      (cocompact Real) (nhds 0) := by
    simpa only [Real.rpow_natCast] using hpowBase
  have hzeroBase :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (0 : Real)
  have hzero : Tendsto
      (fun x : Real => Real.exp (-b * x ^ 2))
      (cocompact Real) (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using hzeroBase
  have hmajor : Tendsto
      (fun x : Real =>
        2 ^ (n - 1) *
          (abs x ^ n * Real.exp (-b * x ^ 2) +
            3 ^ n * Real.exp (-b * x ^ 2)))
      (cocompact Real) (nhds 0) := by
    convert (hpow.add (hzero.const_mul (3 ^ n))).const_mul (2 ^ (n - 1)) using 1 <;>
      ring
  exact squeeze_zero
    (fun x => mul_nonneg (pow_nonneg (by positivity) n) (Real.exp_pos _).le)
    (fun x => by
      have hadd := add_pow_le (abs_nonneg x) (by norm_num : (0 : Real) <= 3) n
      exact (mul_le_mul_of_nonneg_right hadd (Real.exp_pos _).le).trans_eq (by ring))
    hmajor

private theorem tendsto_xiArchimedeanSpectralIntegrand_verticalIntegral_right
    (p : Polynomial Real) :
    Tendsto
      (fun T : Real => intervalIntegral
        (fun y : Real =>
          guinandWeilXiArchimedeanSpectralIntegrand p
            ((T : Complex) + (y : Complex) * Complex.I))
        (-(3 / 4 : Real)) 0 volume)
      atTop (nhds 0) := by
  rcases exists_pos_const_norm_xiArchimedeanSpectralIntegrand_strip_le p with
    ⟨A, hA, hbound⟩
  let M : Real -> Real := fun T =>
    (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
      Real.exp (-(Real.pi / 2) * T ^ 2)
  have hM : Tendsto M atTop (nhds 0) := by
    have h : Tendsto M (cocompact Real) (nhds 0) :=
      tendsto_abs_add_three_pow_mul_exp_neg_mul_sq_cocompact
      (guinandWeilPiEvenPolynomial p).natDegree
      (b := Real.pi / 2) (by positivity)
    exact h.mono_left atTop_le_cocompact
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun T => norm_nonneg _)
    (fun T => by
      refine intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -(3 / 4 : Real)) (b := 0) (C := A * M T) ?_
      intro y hy
      have hy' := Set.uIoc_subset_uIcc hy
      rw [Set.uIcc_of_le (by norm_num)] at hy'
      simpa only [M, mul_assoc] using hbound T y hy'.1 hy'.2)
  rw [show (fun T => A * M T * abs (0 - -(3 / 4 : Real))) =
      fun T => (A * (3 / 4 : Real)) * M T by
    funext T
    norm_num
    ring]
  simpa only [mul_zero] using hM.const_mul (A * (3 / 4 : Real))

private theorem tendsto_xiArchimedeanSpectralIntegrand_verticalIntegral_left
    (p : Polynomial Real) :
    Tendsto
      (fun T : Real => intervalIntegral
        (fun y : Real =>
          guinandWeilXiArchimedeanSpectralIntegrand p
            ((-T : Real) + (y : Complex) * Complex.I))
        (-(3 / 4 : Real)) 0 volume)
      atTop (nhds 0) := by
  rcases exists_pos_const_norm_xiArchimedeanSpectralIntegrand_strip_le p with
    ⟨A, hA, hbound⟩
  let M : Real -> Real := fun T =>
    (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
      Real.exp (-(Real.pi / 2) * T ^ 2)
  have hM : Tendsto M atTop (nhds 0) := by
    have h : Tendsto M (cocompact Real) (nhds 0) :=
      tendsto_abs_add_three_pow_mul_exp_neg_mul_sq_cocompact
      (guinandWeilPiEvenPolynomial p).natDegree
      (b := Real.pi / 2) (by positivity)
    exact h.mono_left atTop_le_cocompact
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun T => norm_nonneg _)
    (fun T => by
      refine intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -(3 / 4 : Real)) (b := 0) (C := A * M T) ?_
      intro y hy
      have hy' := Set.uIoc_subset_uIcc hy
      rw [Set.uIcc_of_le (by norm_num)] at hy'
      have h := hbound (-T) y hy'.1 hy'.2
      simpa only [M, abs_neg, neg_sq, mul_assoc] using h)
  rw [show (fun T => A * M T * abs (0 - -(3 / 4 : Real))) =
      fun T => (A * (3 / 4 : Real)) * M T by
    funext T
    norm_num
    ring]
  simpa only [mul_zero] using hM.const_mul (A * (3 / 4 : Real))

/--
The complete right-line Archimedean integral shifts to the critical line.
Both remote edges vanish by the unconditional digamma bound above.
-/
theorem integral_xiArchimedeanSpectralIntegrand_shifted_eq_real
    (p : Polynomial Real) :
    (MeasureTheory.integral volume fun x : Real =>
      guinandWeilXiArchimedeanSpectralIntegrand p
        ((x : Complex) - (3 / 4 : Real) * Complex.I)) =
      MeasureTheory.integral volume fun x : Real =>
        guinandWeilXiArchimedeanSpectralIntegrand p (x : Complex) := by
  let B : Real -> Complex := fun T => intervalIntegral
    (fun x : Real =>
      guinandWeilXiArchimedeanSpectralIntegrand p
        ((x : Complex) - (3 / 4 : Real) * Complex.I)) (-T) T volume
  let C : Real -> Complex := fun T => intervalIntegral
    (fun x : Real =>
      guinandWeilXiArchimedeanSpectralIntegrand p (x : Complex)) (-T) T volume
  let Vplus : Real -> Complex := fun T => intervalIntegral
    (fun y : Real =>
      guinandWeilXiArchimedeanSpectralIntegrand p
        ((T : Complex) + (y : Complex) * Complex.I)) (-(3 / 4 : Real)) 0 volume
  let Vminus : Real -> Complex := fun T => intervalIntegral
    (fun y : Real =>
      guinandWeilXiArchimedeanSpectralIntegrand p
        ((-T : Real) + (y : Complex) * Complex.I)) (-(3 / 4 : Real)) 0 volume
  have hrectangle (T : Real) :
      B T - C T + Complex.I * Vplus T - Complex.I * Vminus T = 0 := by
    have hdiff : DifferentiableOn Complex
        (guinandWeilXiArchimedeanSpectralIntegrand p)
        (Complex.Rectangle
          ((-T : Complex) - (3 / 4 : Real) * Complex.I) (T : Complex)) := by
      apply (differentiableOn_xiArchimedeanSpectralIntegrand_strip p).mono
      intro z hz
      rw [Complex.Rectangle, Complex.mem_reProdIm] at hz
      have him := hz.2
      norm_num at him
      exact him
    have h := guinandWeilRectangleIntegral_eq_zero_of_differentiableOn hdiff
    simpa only [guinandWeilRectangleIntegral, guinandWeilHorizontalIntegral,
      guinandWeilVerticalIntegral, B, C, Vplus, Vminus,
      Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      ofReal_ofNat, I_re, mul_zero, sub_zero, Complex.sub_im,
      Complex.neg_im, Complex.ofReal_im, Complex.mul_im, I_im, mul_one,
      zero_sub, neg_zero, zero_add, add_zero, Complex.ofReal_neg,
      sub_eq_add_neg, ofReal_zero, zero_mul, Complex.add_re,
      Complex.add_im, neg_mul] using h
  have hfinite : B = fun T =>
      C T - Complex.I * Vplus T + Complex.I * Vminus T := by
    funext T
    have h := hrectangle T
    linear_combination h
  have hBint : Integrable fun x : Real =>
      guinandWeilXiArchimedeanSpectralIntegrand p
        ((x : Complex) - (3 / 4 : Real) * Complex.I) := by
    simpa only [sub_eq_add_neg, neg_mul, ofReal_neg] using
      (integrable_xiArchimedeanSpectralIntegrand_horizontalLine p
        (y := -(3 / 4 : Real)) (by norm_num) (by norm_num))
  have hCint : Integrable fun x : Real =>
      guinandWeilXiArchimedeanSpectralIntegrand p (x : Complex) := by
    simpa only [ofReal_zero, zero_mul, add_zero] using
      (integrable_xiArchimedeanSpectralIntegrand_horizontalLine p
        (y := 0) (by norm_num) (by norm_num))
  refine tendsto_nhds_unique
    (by simpa only [id_eq] using
      (intervalIntegral_tendsto_integral hBint tendsto_neg_atTop_atBot tendsto_id)) ?_
  change Tendsto B atTop _
  rw [hfinite]
  have hC := intervalIntegral_tendsto_integral
    hCint tendsto_neg_atTop_atBot tendsto_id
  have hVplus :=
    (tendsto_xiArchimedeanSpectralIntegrand_verticalIntegral_right p).const_mul
      Complex.I
  have hVminus :=
    (tendsto_xiArchimedeanSpectralIntegrand_verticalIntegral_left p).const_mul
      Complex.I
  simpa only [C, Vplus, Vminus, id_eq, mul_zero, sub_zero, add_zero] using
    (hC.sub hVplus).add hVminus

/-- The Archimedean contour shift in the actual xi right-line coordinate. -/
theorem integral_xiContourWeight_archimedean_right_eq_critical
    (p : Polynomial Real) :
    (MeasureTheory.integral volume fun t : Real =>
      guinandWeilXiContourWeight p
          ((5 / 4 : Real) + (t : Complex) * Complex.I) *
        (-(Real.log Real.pi : Complex) / 2 +
          Complex.digamma
            ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I) / 2)) =
      MeasureTheory.integral volume fun t : Real =>
        guinandWeilPiPolynomialGaussianSource
            (guinandWeilPiEvenPolynomial p) (t : Complex) *
          guinandWeilGammaLogDerivative t := by
  have hshift := integral_xiArchimedeanSpectralIntegrand_shifted_eq_real p
  have hright :
      (fun t : Real =>
        guinandWeilXiArchimedeanSpectralIntegrand p
          ((t : Complex) - (3 / 4 : Real) * Complex.I)) =
        fun t : Real =>
          guinandWeilXiContourWeight p
              ((5 / 4 : Real) + (t : Complex) * Complex.I) *
            (-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I) / 2) := by
    funext t
    unfold guinandWeilXiArchimedeanSpectralIntegrand
      guinandWeilXiArchimedeanSpectralFactor guinandWeilXiContourWeight
    rw [guinandWeilXiContourCoordinate_horizontal]
    congr 2 <;> push_cast <;> ring_nf
    rw [show Complex.I ^ 2 = (-1 : Complex) by norm_num]
    ring
  have hcritical :
      (fun t : Real =>
        guinandWeilXiArchimedeanSpectralIntegrand p (t : Complex)) =
        fun t : Real =>
          guinandWeilPiPolynomialGaussianSource
              (guinandWeilPiEvenPolynomial p) (t : Complex) *
            guinandWeilGammaLogDerivative t := by
    funext t
    unfold guinandWeilXiArchimedeanSpectralIntegrand
      guinandWeilXiArchimedeanSpectralFactor
    rw [guinandWeilGammaLogDerivative_eq_digamma]
    congr 3 <;> push_cast <;> ring
  simpa only [hright, hcritical] using hshift

/-- The complete Gamma/digamma contribution on the xi right vertical is integrable. -/
theorem integrable_xiContourWeight_archimedean_right
    (p : Polynomial Real) :
    Integrable fun t : Real =>
      guinandWeilXiContourWeight p
          ((5 / 4 : Real) + (t : Complex) * Complex.I) *
        (-(Real.log Real.pi : Complex) / 2 +
          Complex.digamma
            ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I) / 2) := by
  have hshift : Integrable fun t : Real =>
      guinandWeilXiArchimedeanSpectralIntegrand p
        ((t : Complex) - (3 / 4 : Real) * Complex.I) := by
    simpa only [sub_eq_add_neg, neg_mul, ofReal_neg] using
      (integrable_xiArchimedeanSpectralIntegrand_horizontalLine p
        (y := -(3 / 4 : Real)) (by norm_num) (by norm_num))
  have hright :
      (fun t : Real =>
        guinandWeilXiArchimedeanSpectralIntegrand p
          ((t : Complex) - (3 / 4 : Real) * Complex.I)) =
        fun t : Real =>
          guinandWeilXiContourWeight p
              ((5 / 4 : Real) + (t : Complex) * Complex.I) *
            (-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I) / 2) := by
    funext t
    unfold guinandWeilXiArchimedeanSpectralIntegrand
      guinandWeilXiArchimedeanSpectralFactor guinandWeilXiContourWeight
    rw [guinandWeilXiContourCoordinate_horizontal]
    congr 2 <;> push_cast <;> ring_nf
    rw [show Complex.I ^ 2 = (-1 : Complex) by norm_num]
    ring
  simpa only [hright] using hshift

/--
After pairing the reflected vertical line, the right Archimedean contribution
is exactly the checked literature Gamma side.
-/
theorem one_div_pi_mul_re_integral_xiContourWeight_archimedean_right_eq_literatureGamma
    (p : Polynomial Real) :
    (1 / Real.pi) *
        (MeasureTheory.integral volume fun t : Real =>
          guinandWeilXiContourWeight p
              ((5 / 4 : Real) + (t : Complex) * Complex.I) *
            (-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I) / 2)).re =
      guinandWeilLiteratureGammaSide
        (guinandWeilPiEvenPolynomialGaussianSchwartz p) := by
  rw [guinandWeilLiteratureGammaSide_eq_digammaIntegral]
  have hshift := integral_xiContourWeight_archimedean_right_eq_critical p
  rw [hshift]
  have hcriticalInt : Integrable fun t : Real =>
      guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p) (t : Complex) *
        guinandWeilGammaLogDerivative t := by
    have h := integrable_xiArchimedeanSpectralIntegrand_horizontalLine
      p (y := 0) (by norm_num) (by norm_num)
    have hcritical :
        (fun t : Real =>
          guinandWeilXiArchimedeanSpectralIntegrand p (t : Complex)) =
          fun t : Real =>
            guinandWeilPiPolynomialGaussianSource
                (guinandWeilPiEvenPolynomial p) (t : Complex) *
              guinandWeilGammaLogDerivative t := by
      funext t
      unfold guinandWeilXiArchimedeanSpectralIntegrand
        guinandWeilXiArchimedeanSpectralFactor
      rw [guinandWeilGammaLogDerivative_eq_digamma]
      congr 3 <;> push_cast <;> ring
    simpa only [ofReal_zero, zero_mul, add_zero, hcritical] using h
  apply congrArg (fun r : Real => (1 / Real.pi) * r)
  calc
    (MeasureTheory.integral volume fun t : Real =>
        guinandWeilPiPolynomialGaussianSource
            (guinandWeilPiEvenPolynomial p) (t : Complex) *
          guinandWeilGammaLogDerivative t).re =
        MeasureTheory.integral volume (fun t : Real =>
          (guinandWeilPiPolynomialGaussianSource
              (guinandWeilPiEvenPolynomial p) (t : Complex) *
            guinandWeilGammaLogDerivative t).re) :=
      (integral_re hcriticalInt).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [guinandWeilGammaLogDerivative_eq_digamma]
      rfl

end

end RiemannHypothesisProject
