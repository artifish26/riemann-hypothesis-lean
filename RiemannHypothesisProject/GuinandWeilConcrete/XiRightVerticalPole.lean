import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannHypothesisProject.GuinandWeilConcrete.LiteratureNormalization
import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianContourShift
import RiemannHypothesisProject.GuinandWeilConcrete.WeightedRectangleArgumentPrinciple
import RiemannHypothesisProject.GuinandWeilConcrete.XiContourWeight

/-!
# Rational pole contribution on the xi right vertical

This module evaluates the two elementary rational terms in the right-half-plane
logarithmic derivative of xi.  A finite weighted residue calculation on the
spectral strip is followed by an infinite-rectangle limit using the proved
polynomial-Gaussian strip decay.
-/

namespace RiemannHypothesisProject

open Complex Filter MeasureTheory Set Topology
open scoped Interval Topology

noncomputable section

/-- The two xi rational factors written in the spectral coordinate `z`. -/
noncomputable def guinandWeilXiRationalSpectralIntegrand
    (p : Polynomial Real) (z : Complex) : Complex :=
  guinandWeilPiPolynomialGaussianSource (guinandWeilPiEvenPolynomial p) z *
    (1 / ((1 / 2 : Complex) + Complex.I * z) +
      1 / (-(1 / 2 : Complex) + Complex.I * z))

private def xiRationalPolePolynomial (z : Complex) : Complex :=
  (z - Complex.I / 2) * (z + Complex.I / 2)

private theorem differentiable_xiRationalPolePolynomial :
    Differentiable Complex xiRationalPolePolynomial := by
  unfold xiRationalPolePolynomial
  fun_prop

private theorem logDeriv_xiRationalPolePolynomial
    {z : Complex} (hpos : z ≠ Complex.I / 2)
    (hneg : z ≠ -Complex.I / 2) :
    logDeriv xiRationalPolePolynomial z =
      1 / (z - Complex.I / 2) + 1 / (z + Complex.I / 2) := by
  unfold xiRationalPolePolynomial
  have hplus : z + Complex.I / 2 ≠ 0 := by
    intro hzero
    apply hneg
    linear_combination hzero
  rw [logDeriv_mul
    (f := fun z : Complex => z - Complex.I / 2)
    (g := fun z : Complex => z + Complex.I / 2) z
    (sub_ne_zero.mpr hpos) hplus
    (differentiableAt_id.sub_const _) (differentiableAt_id.add_const _)]
  simp only [logDeriv_apply, deriv_sub_const, deriv_add_const, deriv_id'', one_div]

private theorem xiRationalPolePolynomial_zero_iff
    (z : Complex) :
    xiRationalPolePolynomial z = 0 <->
      z = Complex.I / 2 \/ z = -Complex.I / 2 := by
  unfold xiRationalPolePolynomial
  rw [mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      linear_combination h
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h]
      ring

private theorem analyticOrderAt_xiRationalPolePolynomial_ne_top
    (z : Complex) :
    analyticOrderAt xiRationalPolePolynomial z ≠ ⊤ := by
  apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr
    differentiable_xiRationalPolePolynomial).analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (x := (0 : Complex)) (y := z) trivial trivial
  rw [(differentiable_xiRationalPolePolynomial.analyticAt 0).analyticOrderAt_eq_zero.mpr]
  · exact ENat.zero_ne_top
  · norm_num [xiRationalPolePolynomial, Complex.ext_iff]

private theorem analyticOrderNatAt_xiRationalPolePolynomial_neg_I_half :
    analyticOrderNatAt xiRationalPolePolynomial (-Complex.I / 2) = 1 := by
  have han := differentiable_xiRationalPolePolynomial.analyticAt (-Complex.I / 2)
  have hzero : xiRationalPolePolynomial (-Complex.I / 2) = 0 := by
    unfold xiRationalPolePolynomial
    ring_nf
  have hderiv : deriv xiRationalPolePolynomial (-Complex.I / 2) ≠ 0 := by
    unfold xiRationalPolePolynomial
    have hd :=
      ((hasDerivAt_id (-Complex.I / 2)).sub_const (Complex.I / 2)).mul
        ((hasDerivAt_id (-Complex.I / 2)).add_const (Complex.I / 2))
    change HasDerivAt
      (fun z : Complex => (z - Complex.I / 2) * (z + Complex.I / 2))
      (1 * ((-Complex.I / 2) + Complex.I / 2) +
        ((-Complex.I / 2) - Complex.I / 2) * 1)
      (-Complex.I / 2) at hd
    rw [hd.deriv]
    norm_num [Complex.ext_iff]
  have horder := han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv
  rw [analyticOrderNatAt, horder]
  simp

private theorem neg_I_half_mem_spectralRectangle_nhds
    {T : Real} (hT : 0 < T) :
    Complex.Rectangle
        ((-T : Complex) - (3 / 4 : Real) * Complex.I) (T : Complex) ∈
      nhds (-Complex.I / 2) := by
  rw [guinandWeilRectangle_mem_nhds_iff]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, ofReal_ofNat,
    I_re, mul_zero, sub_zero, Complex.neg_re, Complex.sub_im,
    Complex.ofReal_im, Complex.mul_im, I_im, mul_one, zero_sub, Complex.neg_im,
    Complex.div_re, Complex.div_im]
  rw [Set.uIoo_of_le (by linarith), Set.uIoo_of_le (by norm_num)]
  constructor <;> constructor <;> norm_num <;> linarith

private theorem pos_I_half_not_mem_spectralRectangle
    (T : Real) :
    Complex.I / 2 ∉
      Complex.Rectangle
        ((-T : Complex) - (3 / 4 : Real) * Complex.I) (T : Complex) := by
  intro hmem
  rw [Complex.Rectangle, Complex.mem_reProdIm] at hmem
  have him := hmem.2
  rw [Set.uIcc_of_le (by norm_num)] at him
  norm_num at him

private theorem normalizedRectangle_xiRationalSpectralIntegrand
    (p : Polynomial Real) {T : Real} (hT : 0 < T) :
    guinandWeilNormalizedRectangleIntegral
        (guinandWeilXiRationalSpectralIntegrand p)
        ((-T : Complex) - (3 / 4 : Real) * Complex.I) (T : Complex) =
      -Complex.I *
        guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p) (-Complex.I / 2) := by
  let zT : Complex := (-T : Complex) - (3 / 4 : Real) * Complex.I
  let wT : Complex := T
  let H : Complex -> Complex :=
    guinandWeilPiPolynomialGaussianSource (guinandWeilPiEvenPolynomial p)
  have hzre : zT.re <= wT.re := by
    dsimp [zT, wT]
    simp
    linarith
  have hzim : zT.im <= wT.im := by
    norm_num [zT, wT]
  have hpN : Complex.Rectangle zT wT ∈ nhds (-Complex.I / 2) := by
    simpa [zT, wT] using neg_I_half_mem_spectralRectangle_nhds hT
  have hweighted :=
    guinandWeilNormalizedRectangleIntegral_weight_mul_logDeriv_eq_sum
      (H := H) (f := xiRationalPolePolynomial)
      (S := {-Complex.I / 2}) hzre hzim
      ((analyticOnNhd_guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p)).mono (by simp [H]))
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        differentiable_xiRationalPolePolynomial).mono (by simp))
      (fun s _ => analyticOrderAt_xiRationalPolePolynomial_ne_top s)
      (by
        intro s hs
        have hs' : s = -Complex.I / 2 := by simpa using hs
        subst s
        simpa [zT, wT] using mem_of_mem_nhds hpN)
      (by
        intro s hs
        simp only [Finset.mem_singleton]
        rw [xiRationalPolePolynomial_zero_iff]
        constructor
        · intro h
          exact Or.inr h
        · rintro (h | h)
          · exact (pos_I_half_not_mem_spectralRectangle T
              (by simpa [zT, wT, h] using hs)).elim
          · exact h)
      (by
        intro s hs hzero
        have hsR := guinandWeilRectangleBorder_subset_rectangle zT wT hs
        have hsPole : s = -Complex.I / 2 := by
          have hz := (xiRationalPolePolynomial_zero_iff s).mp hzero
          rcases hz with hpos | hneg
          · exact (pos_I_half_not_mem_spectralRectangle T (by simpa [zT, wT, hpos] using hsR)).elim
          · exact hneg
        subst s
        exact (not_mem_guinandWeilRectangleBorder_of_rectangle_mem_nhds
          hzre hzim hpN) hs)
  have hweighted' :
      guinandWeilNormalizedRectangleIntegral
          (fun z => H z * logDeriv xiRationalPolePolynomial z) zT wT =
        H (-Complex.I / 2) := by
    simpa [analyticOrderNatAt_xiRationalPolePolynomial_neg_I_half] using hweighted
  have hcongr : Set.EqOn
      (guinandWeilXiRationalSpectralIntegrand p)
      (fun z => -Complex.I * (H z * logDeriv xiRationalPolePolynomial z))
      (guinandWeilRectangleBorder zT wT) := by
    intro z hz
    have hzR := guinandWeilRectangleBorder_subset_rectangle zT wT hz
    have hpos : z ≠ Complex.I / 2 := by
      intro heq
      exact pos_I_half_not_mem_spectralRectangle T (by simpa [zT, wT, heq] using hzR)
    have hneg : z ≠ -Complex.I / 2 := by
      intro heq
      subst z
      exact (not_mem_guinandWeilRectangleBorder_of_rectangle_mem_nhds
        hzre hzim hpN) hz
    have hplus : z + Complex.I / 2 ≠ 0 := by
      intro hzero
      apply hneg
      linear_combination hzero
    change guinandWeilXiRationalSpectralIntegrand p z =
      -Complex.I * (H z * logDeriv xiRationalPolePolynomial z)
    rw [logDeriv_xiRationalPolePolynomial hpos hneg]
    dsimp only [guinandWeilXiRationalSpectralIntegrand, H]
    rw [show (1 / 2 : Complex) + Complex.I * z =
        Complex.I * (z - Complex.I / 2) by
          apply Complex.ext <;> simp <;> ring,
      show -(1 / 2 : Complex) + Complex.I * z =
        Complex.I * (z + Complex.I / 2) by
          apply Complex.ext <;> simp <;> ring]
    field_simp [sub_ne_zero.mpr hpos, hplus, Complex.I_ne_zero]
    simp only [pow_two, Complex.I_mul_I]
    ring
  rw [guinandWeilNormalizedRectangleIntegral_congr hcongr]
  calc
    guinandWeilNormalizedRectangleIntegral
        (fun z => -Complex.I * (H z * logDeriv xiRationalPolePolynomial z)) zT wT =
      -Complex.I * guinandWeilNormalizedRectangleIntegral
        (fun z => H z * logDeriv xiRationalPolePolynomial z) zT wT := by
          unfold guinandWeilNormalizedRectangleIntegral guinandWeilRectangleIntegral
            guinandWeilHorizontalIntegral guinandWeilVerticalIntegral
          simp only [intervalIntegral.integral_const_mul]
          ring
    _ = -Complex.I * H (-Complex.I / 2) := by rw [hweighted']

private theorem norm_xiRationalSpectralFactor_horizontalLine_le_eight
    (t y : Real) (hy : y = 0 \/ y = -(3 / 4 : Real)) :
    norm
        (1 / ((1 / 2 : Complex) + Complex.I *
            ((t : Complex) + (y : Complex) * Complex.I)) +
          1 / (-(1 / 2 : Complex) + Complex.I *
            ((t : Complex) + (y : Complex) * Complex.I))) <= 8 := by
  let d1 : Complex :=
    (1 / 2 : Complex) + Complex.I *
      ((t : Complex) + (y : Complex) * Complex.I)
  let d2 : Complex :=
    -(1 / 2 : Complex) + Complex.I *
      ((t : Complex) + (y : Complex) * Complex.I)
  have hd1 : (1 / 4 : Real) <= norm d1 := by
    calc
      (1 / 4 : Real) <= abs d1.re := by
        rcases hy with rfl | rfl <;> norm_num [d1]
      _ <= norm d1 := Complex.abs_re_le_norm d1
  have hd2 : (1 / 4 : Real) <= norm d2 := by
    calc
      (1 / 4 : Real) <= abs d2.re := by
        rcases hy with rfl | rfl <;> norm_num [d2]
      _ <= norm d2 := Complex.abs_re_le_norm d2
  have hd1pos : 0 < norm d1 := lt_of_lt_of_le (by norm_num) hd1
  have hd2pos : 0 < norm d2 := lt_of_lt_of_le (by norm_num) hd2
  have hinv1 : norm (1 / d1) <= 4 := by
    rw [one_div, norm_inv]
    exact (inv_le_iff_one_le_mul₀' hd1pos).2 (by nlinarith)
  have hinv2 : norm (1 / d2) <= 4 := by
    rw [one_div, norm_inv]
    exact (inv_le_iff_one_le_mul₀' hd2pos).2 (by nlinarith)
  change norm (1 / d1 + 1 / d2) <= 8
  exact (norm_add_le _ _).trans (by linarith)

private theorem integrable_xiRationalSpectralIntegrand_horizontalLine
    (p : Polynomial Real) (y : Real) (hy : y = 0 \/ y = -(3 / 4 : Real)) :
    Integrable fun t : Real =>
      guinandWeilXiRationalSpectralIntegrand p
        ((t : Complex) + (y : Complex) * Complex.I) := by
  let q : Polynomial Complex := guinandWeilPiEvenPolynomial p
  have hsource : Integrable fun t : Real =>
      guinandWeilPiPolynomialGaussianSource q
        ((t : Complex) + (y : Complex) * Complex.I) := by
    have h :=
      integrable_guinandWeilPiPolynomialGaussianSource_horizontalLine_mul_exp
        q 0 y
    simpa only [ofReal_zero, zero_mul, mul_zero, Complex.exp_zero, mul_one] using h
  have hmajor : Integrable fun t : Real =>
      8 * norm (guinandWeilPiPolynomialGaussianSource q
        ((t : Complex) + (y : Complex) * Complex.I)) :=
    hsource.norm.const_mul 8
  refine hmajor.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hd1 (t : Real) :
        (1 / 2 : Complex) + Complex.I *
            ((t : Complex) + (y : Complex) * Complex.I) ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      rcases hy with rfl | rfl <;> norm_num at hre
    have hd2 (t : Real) :
        -(1 / 2 : Complex) + Complex.I *
            ((t : Complex) + (y : Complex) * Complex.I) ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      rcases hy with rfl | rfl <;> norm_num at hre
    have hcontinuous : Continuous fun t : Real =>
        guinandWeilXiRationalSpectralIntegrand p
          ((t : Complex) + (y : Complex) * Complex.I) := by
      unfold guinandWeilXiRationalSpectralIntegrand
      have hsourceContinuous : Continuous fun t : Real =>
          guinandWeilPiPolynomialGaussianSource
            (guinandWeilPiEvenPolynomial p)
            ((t : Complex) + (y : Complex) * Complex.I) :=
        ((guinandWeilPiEvenPolynomial p).differentiable_aeval.mul
          differentiable_guinandWeilPiGaussianSource).continuous.comp (by fun_prop)
      exact hsourceContinuous.mul (by fun_prop (disch := aesop))
    exact hcontinuous.aestronglyMeasurable
  · simp only [guinandWeilXiRationalSpectralIntegrand, norm_mul]
    have hfactor :=
      norm_xiRationalSpectralFactor_horizontalLine_le_eight t y hy
    have hsource_nonneg := norm_nonneg
      (guinandWeilPiPolynomialGaussianSource q
        ((t : Complex) + (y : Complex) * Complex.I))
    dsimp only [q]
    nlinarith

private theorem guinandWeilXiRationalSpectralIntegrand_real_neg
    (p : Polynomial Real) (t : Real) :
    guinandWeilXiRationalSpectralIntegrand p (-t : Complex) =
      -guinandWeilXiRationalSpectralIntegrand p (t : Complex) := by
  have hd1 : (1 / 2 : Complex) + Complex.I * (t : Complex) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
  have hd2 : -(1 / 2 : Complex) + Complex.I * (t : Complex) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
  have hd1neg : (1 / 2 : Complex) + Complex.I * (-t : Complex) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
  have hd2neg : -(1 / 2 : Complex) + Complex.I * (-t : Complex) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
  unfold guinandWeilXiRationalSpectralIntegrand
  rw [guinandWeilPiEvenPolynomialGaussianSource_neg]
  rw [show (1 / 2 : Complex) + Complex.I * (-t : Complex) =
      -(-(1 / 2 : Complex) + Complex.I * (t : Complex)) by ring,
    show -(1 / 2 : Complex) + Complex.I * (-t : Complex) =
      -((1 / 2 : Complex) + Complex.I * (t : Complex)) by ring]
  simp only [one_div, inv_neg]
  ring

private theorem integral_xiRationalSpectralIntegrand_real_eq_zero
    (p : Polynomial Real) :
    (MeasureTheory.integral volume fun t : Real =>
      guinandWeilXiRationalSpectralIntegrand p (t : Complex)) = 0 := by
  have hreflect :
      (MeasureTheory.integral volume fun t : Real =>
          guinandWeilXiRationalSpectralIntegrand p (-t : Complex)) =
        MeasureTheory.integral volume fun t : Real =>
          guinandWeilXiRationalSpectralIntegrand p (t : Complex) := by
    simpa only [ofReal_neg] using
      (integral_neg_eq_self
        (f := fun t : Real =>
          guinandWeilXiRationalSpectralIntegrand p (t : Complex)) volume)
  have hneg :
      (MeasureTheory.integral volume fun t : Real =>
          guinandWeilXiRationalSpectralIntegrand p (-t : Complex)) =
        -(MeasureTheory.integral volume fun t : Real =>
          guinandWeilXiRationalSpectralIntegrand p (t : Complex)) := by
    rw [show (fun t : Real =>
        guinandWeilXiRationalSpectralIntegrand p (-t : Complex)) =
      fun t : Real =>
        -guinandWeilXiRationalSpectralIntegrand p (t : Complex) by
      funext t
      exact guinandWeilXiRationalSpectralIntegrand_real_neg p t]
    exact MeasureTheory.integral_neg (μ := volume) _
  have hself := hreflect.symm.trans hneg
  have htwo : (2 : Complex) *
      (MeasureTheory.integral volume fun t : Real =>
        guinandWeilXiRationalSpectralIntegrand p (t : Complex)) = 0 := by
    linear_combination hself
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

private theorem norm_xiRationalSpectralFactor_verticalLine_le_two
    (x y : Real) (hx : 1 <= abs x) :
    norm
        (1 / ((1 / 2 : Complex) + Complex.I *
            ((x : Complex) + (y : Complex) * Complex.I)) +
          1 / (-(1 / 2 : Complex) + Complex.I *
            ((x : Complex) + (y : Complex) * Complex.I))) <= 2 := by
  let d1 : Complex :=
    (1 / 2 : Complex) + Complex.I *
      ((x : Complex) + (y : Complex) * Complex.I)
  let d2 : Complex :=
    -(1 / 2 : Complex) + Complex.I *
      ((x : Complex) + (y : Complex) * Complex.I)
  have hd1 : 1 <= norm d1 := by
    calc
      1 <= abs x := hx
      _ = abs d1.im := by simp [d1]
      _ <= norm d1 := Complex.abs_im_le_norm d1
  have hd2 : 1 <= norm d2 := by
    calc
      1 <= abs x := hx
      _ = abs d2.im := by simp [d2]
      _ <= norm d2 := Complex.abs_im_le_norm d2
  have hd1pos : 0 < norm d1 := lt_of_lt_of_le zero_lt_one hd1
  have hd2pos : 0 < norm d2 := lt_of_lt_of_le zero_lt_one hd2
  have hinv1 : norm (1 / d1) <= 1 := by
    rw [one_div, norm_inv, inv_le_one₀ hd1pos]
    exact hd1
  have hinv2 : norm (1 / d2) <= 1 := by
    rw [one_div, norm_inv, inv_le_one₀ hd2pos]
    exact hd2
  change norm (1 / d1 + 1 / d2) <= 2
  exact (norm_add_le _ _).trans (by linarith)

private theorem tendsto_xiRationalSpectralIntegrand_verticalIntegral_right
    (p : Polynomial Real) :
    Tendsto
      (fun T : Real => intervalIntegral (fun y : Real =>
        guinandWeilXiRationalSpectralIntegrand p
          ((T : Complex) + (y : Complex) * Complex.I))
        (-(3 / 4 : Real)) 0 volume)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine Metric.tendsto_atTop.mpr ?_
  intro epsilon hepsilon
  have hsmall :=
    eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_le_of_horizontalStrip
      (guinandWeilPiEvenPolynomial p) 0 (A := (3 / 4 : Real))
      (epsilon := epsilon / 4) (by norm_num) (by positivity)
  have hsmall_atTop := hsmall.filter_mono atTop_le_cocompact
  rcases eventually_atTop.1
      (hsmall_atTop.and (eventually_ge_atTop (1 : Real))) with ⟨N, hN⟩
  refine ⟨N, fun T hTN => ?_⟩
  rcases hN T hTN with ⟨hT, hTone⟩
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(3 / 4 : Real)) (b := 0) (C := epsilon / 2) ?_).trans_lt ?_
  · intro y hy
    have hy_abs : abs y <= (3 / 4 : Real) := by
      have hy' := Set.uIoc_subset_uIcc hy
      rw [Set.uIcc_of_le (by norm_num)] at hy'
      rw [abs_le]
      exact ⟨hy'.1, hy'.2.trans (by norm_num)⟩
    have hsource := hT y hy_abs
    simp only [pow_zero, mul_one] at hsource
    have hfactor :=
      norm_xiRationalSpectralFactor_verticalLine_le_two T y
        (by
          rw [abs_of_nonneg (le_trans zero_le_one hTone)]
          exact hTone)
    simp only [guinandWeilXiRationalSpectralIntegrand, norm_mul]
    nlinarith [norm_nonneg
      (guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p)
        ((T : Complex) + (y : Complex) * Complex.I))]
  · norm_num
    nlinarith

private theorem tendsto_xiRationalSpectralIntegrand_verticalIntegral_left
    (p : Polynomial Real) :
    Tendsto
      (fun T : Real => intervalIntegral (fun y : Real =>
        guinandWeilXiRationalSpectralIntegrand p
          ((-T : Real) + (y : Complex) * Complex.I))
        (-(3 / 4 : Real)) 0 volume)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine Metric.tendsto_atTop.mpr ?_
  intro epsilon hepsilon
  have hsmall :=
    eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_le_of_horizontalStrip
      (guinandWeilPiEvenPolynomial p) 0 (A := (3 / 4 : Real))
      (epsilon := epsilon / 4) (by norm_num) (by positivity)
  have hneg : Tendsto (fun T : Real => -T) atTop atBot := tendsto_neg_atTop_atBot
  have hcocompact : Tendsto (fun T : Real => -T) atTop (cocompact Real) :=
    hneg.mono_right atBot_le_cocompact
  have hsmall_atTop := hcocompact.eventually hsmall
  rcases eventually_atTop.1
      (hsmall_atTop.and (eventually_ge_atTop (1 : Real))) with ⟨N, hN⟩
  refine ⟨N, fun T hTN => ?_⟩
  rcases hN T hTN with ⟨hT, hTone⟩
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(3 / 4 : Real)) (b := 0) (C := epsilon / 2) ?_).trans_lt ?_
  · intro y hy
    have hy_abs : abs y <= (3 / 4 : Real) := by
      have hy' := Set.uIoc_subset_uIcc hy
      rw [Set.uIcc_of_le (by norm_num)] at hy'
      rw [abs_le]
      exact ⟨hy'.1, hy'.2.trans (by norm_num)⟩
    have hsource := hT y hy_abs
    simp only [pow_zero, mul_one] at hsource
    have hfactor :=
      norm_xiRationalSpectralFactor_verticalLine_le_two (-T) y (by
        rw [abs_neg, abs_of_nonneg (le_trans zero_le_one hTone)]
        exact hTone)
    simp only [guinandWeilXiRationalSpectralIntegrand, norm_mul]
    nlinarith [norm_nonneg
      (guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p)
        ((-T : Real) + (y : Complex) * Complex.I))]
  · norm_num
    nlinarith

/--
The complete shifted spectral-line integral of the two rational xi terms is
the residue at `-I/2`, with the exact one-right-line factor `1/(2*pi)`.
-/
theorem one_div_two_pi_mul_integral_xiRationalSpectralIntegrand_shifted
    (p : Polynomial Real) :
    (1 / (2 * Real.pi) : Complex) *
        (MeasureTheory.integral volume fun t : Real =>
          guinandWeilXiRationalSpectralIntegrand p
            ((t : Complex) - (3 / 4 : Real) * Complex.I)) =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p) (-Complex.I / 2) := by
  let B : Real -> Complex := fun T => intervalIntegral
    (fun t : Real =>
      guinandWeilXiRationalSpectralIntegrand p
        ((t : Complex) - (3 / 4 : Real) * Complex.I)) (-T) T volume
  let C : Real -> Complex := fun T => intervalIntegral
    (fun t : Real =>
      guinandWeilXiRationalSpectralIntegrand p (t : Complex)) (-T) T volume
  let Vplus : Real -> Complex := fun T => intervalIntegral
    (fun y : Real =>
      guinandWeilXiRationalSpectralIntegrand p
        ((T : Complex) + (y : Complex) * Complex.I)) (-(3 / 4 : Real)) 0 volume
  let Vminus : Real -> Complex := fun T => intervalIntegral
    (fun y : Real =>
      guinandWeilXiRationalSpectralIntegrand p
        ((-T : Real) + (y : Complex) * Complex.I)) (-(3 / 4 : Real)) 0 volume
  let N : Real -> Complex := fun T =>
    (1 / (2 * Real.pi * Complex.I)) *
      (B T - C T + Complex.I * Vplus T - Complex.I * Vminus T)
  let L : Complex := MeasureTheory.integral volume fun t : Real =>
    guinandWeilXiRationalSpectralIntegrand p
      ((t : Complex) - (3 / 4 : Real) * Complex.I)
  have hBint : Integrable fun t : Real =>
      guinandWeilXiRationalSpectralIntegrand p
        ((t : Complex) - (3 / 4 : Real) * Complex.I) := by
    simpa only [sub_eq_add_neg, neg_mul, ofReal_neg] using
      (integrable_xiRationalSpectralIntegrand_horizontalLine
        p (-(3 / 4 : Real)) (Or.inr rfl))
  have hCint : Integrable fun t : Real =>
      guinandWeilXiRationalSpectralIntegrand p (t : Complex) := by
    simpa only [ofReal_zero, zero_mul, add_zero] using
      (integrable_xiRationalSpectralIntegrand_horizontalLine p 0 (Or.inl rfl))
  have hB : Tendsto B atTop (nhds L) := by
    simpa only [B, L, id_eq] using
      (intervalIntegral_tendsto_integral hBint tendsto_neg_atTop_atBot tendsto_id)
  have hC : Tendsto C atTop (nhds 0) := by
    have h :=
      intervalIntegral_tendsto_integral hCint tendsto_neg_atTop_atBot tendsto_id
    rw [integral_xiRationalSpectralIntegrand_real_eq_zero p] at h
    simpa only [C, id_eq] using h
  have hVplus : Tendsto Vplus atTop (nhds 0) := by
    have h := tendsto_xiRationalSpectralIntegrand_verticalIntegral_right p
    simpa only [Vplus] using h
  have hVminus : Tendsto Vminus atTop (nhds 0) := by
    have h := tendsto_xiRationalSpectralIntegrand_verticalIntegral_left p
    simpa only [Vminus] using h
  have hN : Tendsto N atTop
      (nhds ((1 / (2 * Real.pi * Complex.I)) * L)) := by
    have hsum :=
      ((hB.sub hC).add (hVplus.const_mul Complex.I)).sub
        (hVminus.const_mul Complex.I)
    have hscaled := hsum.const_mul (1 / (2 * Real.pi * Complex.I))
    simpa only [N, sub_zero, add_zero, mul_zero] using hscaled
  have hNconstant : Tendsto N atTop
      (nhds (-Complex.I *
        guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p) (-Complex.I / 2))) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
    have hfinite := normalizedRectangle_xiRationalSpectralIntegrand p hT
    unfold guinandWeilNormalizedRectangleIntegral
      guinandWeilRectangleIntegral guinandWeilHorizontalIntegral
      guinandWeilVerticalIntegral at hfinite
    dsimp only [N, B, C, Vplus, Vminus]
    convert hfinite.symm using 1 <;> norm_num
    apply intervalIntegral.integral_congr
    intro x _hx
    congr 1
  have hlimit := tendsto_nhds_unique hN hNconstant
  have hpi : (Real.pi : Complex) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hL : L =
      (2 * Real.pi : Complex) *
        guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p) (-Complex.I / 2) := by
    calc
      L = (2 * Real.pi * Complex.I) *
          ((1 / (2 * Real.pi * Complex.I)) * L) := by
        field_simp [hpi, Complex.I_ne_zero]
      _ = (2 * Real.pi * Complex.I) *
          (-Complex.I *
            guinandWeilPiPolynomialGaussianSource
              (guinandWeilPiEvenPolynomial p) (-Complex.I / 2)) := by
        rw [hlimit]
      _ = (2 * Real.pi : Complex) *
          guinandWeilPiPolynomialGaussianSource
            (guinandWeilPiEvenPolynomial p) (-Complex.I / 2) := by
        ring_nf
        simp [Complex.I_sq]
  change (1 / (2 * Real.pi) : Complex) * L = _
  rw [hL]
  field_simp [hpi]

private theorem xiRationalSpectralIntegrand_shifted_eq_right
    (p : Polynomial Real) :
    (fun t : Real => guinandWeilXiRationalSpectralIntegrand p
      ((t : Complex) - (3 / 4 : Real) * Complex.I)) =
      fun t : Real =>
        guinandWeilXiContourWeight p
            ((5 / 4 : Real) + (t : Complex) * Complex.I) *
          (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
            1 / ((1 / 4 : Real) + (t : Complex) * Complex.I)) := by
  funext t
  unfold guinandWeilXiRationalSpectralIntegrand guinandWeilXiContourWeight
  rw [guinandWeilXiContourCoordinate_horizontal]
  apply congrArg₂ (· * ·)
  · congr 1
    apply Complex.ext <;> simp <;> ring
  · apply congrArg₂ (· + ·)
    · apply congrArg (fun z : Complex => 1 / z)
      apply Complex.ext <;> simp <;> ring
    · apply congrArg (fun z : Complex => 1 / z)
      apply Complex.ext <;> simp <;> ring

/-- The complete rational contribution on the xi right vertical is integrable. -/
theorem integrable_xiContourWeight_rational_right
    (p : Polynomial Real) :
    Integrable fun t : Real =>
      guinandWeilXiContourWeight p
          ((5 / 4 : Real) + (t : Complex) * Complex.I) *
        (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
          1 / ((1 / 4 : Real) + (t : Complex) * Complex.I)) := by
  have hshift : Integrable fun t : Real =>
      guinandWeilXiRationalSpectralIntegrand p
        ((t : Complex) - (3 / 4 : Real) * Complex.I) := by
    simpa only [sub_eq_add_neg, neg_mul, ofReal_neg] using
      (integrable_xiRationalSpectralIntegrand_horizontalLine
        p (-(3 / 4 : Real)) (Or.inr rfl))
  rw [← xiRationalSpectralIntegrand_shifted_eq_right p]
  exact hshift

/-- The rational residue evaluation in the actual xi right-line coordinate. -/
theorem one_div_two_pi_mul_integral_xiContourWeight_rational_right
    (p : Polynomial Real) :
    (1 / (2 * Real.pi) : Complex) *
        (MeasureTheory.integral volume fun t : Real =>
          guinandWeilXiContourWeight p
              ((5 / 4 : Real) + (t : Complex) * Complex.I) *
            (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
              1 / ((1 / 4 : Real) + (t : Complex) * Complex.I))) =
      guinandWeilXiContourWeight p 1 := by
  have hweightOne : guinandWeilXiContourWeight p 1 =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiEvenPolynomial p) (-Complex.I / 2) := by
    unfold guinandWeilXiContourWeight
    congr 1
    apply Complex.ext <;> simp <;> norm_num
  rw [hweightOne, ← xiRationalSpectralIntegrand_shifted_eq_right p]
  exact one_div_two_pi_mul_integral_xiRationalSpectralIntegrand_shifted p

/--
After pairing the reflected vertical line, the rational contribution is
exactly the checked literature pole side at `+I/2` and `-I/2`.
-/
theorem one_div_pi_mul_re_integral_xiContourWeight_rational_right_eq_literaturePole
    (p : Polynomial Real) :
    (1 / Real.pi) *
        (MeasureTheory.integral volume fun t : Real =>
          guinandWeilXiContourWeight p
              ((5 / 4 : Real) + (t : Complex) * Complex.I) *
            (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
              1 / ((1 / 4 : Real) + (t : Complex) * Complex.I))).re =
      guinandWeilPiPolynomialGaussianLiteraturePoleSide
        (guinandWeilPiEvenPolynomial p) := by
  let J : Complex := MeasureTheory.integral volume fun t : Real =>
    guinandWeilXiContourWeight p
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
        1 / ((1 / 4 : Real) + (t : Complex) * Complex.I))
  let H : Complex :=
    guinandWeilPiPolynomialGaussianSource
      (guinandWeilPiEvenPolynomial p) (-Complex.I / 2)
  have hright := one_div_two_pi_mul_integral_xiContourWeight_rational_right p
  have hweightOne : guinandWeilXiContourWeight p 1 = H := by
    unfold guinandWeilXiContourWeight H
    congr 1
    apply Complex.ext <;> simp <;> norm_num
  rw [hweightOne] at hright
  have hright' : J = (2 * Real.pi : Complex) * H := by
    have hpi : (Real.pi : Complex) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    change (1 / (2 * Real.pi) : Complex) * J = H at hright
    field_simp [hpi] at hright
    exact hright
  rw [guinandWeilPiPolynomialGaussianLiteraturePoleSide_eq]
  have heven :
      guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p) (Complex.I / 2) = H := by
    calc
      guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p) (Complex.I / 2) =
        guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial p) (-(Complex.I / 2)) :=
            (guinandWeilPiEvenPolynomialGaussianSource_neg
              p (Complex.I / 2)).symm
      _ = H := by
        unfold H
        congr 1
        ring
  rw [heven]
  change (1 / Real.pi) * J.re = (H + H).re
  rw [hright']
  simp only [mul_re, ofReal_re, ofReal_im, ofReal_ofNat, zero_mul, sub_zero, add_re]
  norm_num
  field_simp [Real.pi_ne_zero]
  ring

end

end RiemannHypothesisProject
