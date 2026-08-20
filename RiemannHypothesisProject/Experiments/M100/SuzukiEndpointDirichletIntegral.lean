import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Distributions.Cauchy
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointComparisonNormalization

/-!
# Classical Dirichlet integral for M100-DF6D4

This module discharges `SuzukiDirichletIntegralSource`.  It evaluates the
exponentially damped sinc integral by Fubini and the Laplace transform of
`sin`, then identifies the ordinary improper integral through an Abel-limit
argument.  Existence of the ordinary limit comes from the explicit nine-step
tail primitive in `SuzukiEndpointComparisonNormalization`.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

private theorem integral_exp_sin_Ioi {s : Real} (hs : 0 < s) :
    (∫ t : Real in Ioi 0, Real.exp (-s * t) * Real.sin t) =
      1 / (s ^ 2 + 1) := by
  let z : Complex := (-s : Real) + Complex.I
  have hz : z.re < 0 := by
    simp [z, hs]
  have h := integral_exp_mul_complex_Ioi (a := z) hz 0
  have him := congrArg Complex.im h
  rw [← RCLike.im_eq_complex_im] at him
  rw [← integral_im (integrableOn_exp_mul_complex_Ioi hz 0)] at him
  have hintegrand :
      (fun t : Real => (RCLike.im : Complex →+ Real)
        (Complex.exp (z * (t : Complex)))) =
        fun t : Real => Real.exp (-s * t) * Real.sin t := by
    funext t
    rw [RCLike.im_eq_complex_im]
    rw [Complex.exp_im]
    simp [z]
  rw [hintegrand] at him
  rw [show Complex.exp (z * (0 : Real)) = 1 by simp] at him
  have hrhs : (RCLike.im : Complex →+ Real) (-1 / z) =
      1 / (s ^ 2 + 1) := by
    rw [RCLike.im_eq_complex_im]
    rw [Complex.div_im]
    simp [z, Complex.normSq_apply]
    field_simp
  rw [hrhs] at him
  exact him

private theorem integrable_damped_sine_product {a : Real} (ha : 0 < a) :
    Integrable
      (fun p : Real × Real => Real.exp (-p.1 * p.2) * Real.sin p.2)
      ((volume.restrict (Ioi a)).prod (volume.restrict (Ioi 0))) := by
  rw [integrable_prod_iff']
  · constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := ht
      have hbase := integrableOn_exp_mul_Ioi (neg_neg_of_pos htpos) a
      have hbase' : IntegrableOn (fun s : Real => Real.exp (-s * t)) (Ioi a) := by
        simpa [mul_comm] using hbase
      exact hbase'.mul_const (Real.sin t)
    · have hmajor := exp_neg_integrableOn_Ioi 0 ha
      let g : Real → Real := fun t => |Real.sin t| * (Real.exp (-a * t) / t)
      have hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
        have hg : Measurable g := by
          dsimp [g]
          fun_prop
        exact hg.aestronglyMeasurable
      have hg_int : Integrable g (volume.restrict (Ioi 0)) := by
        apply MeasureTheory.Integrable.mono hmajor hg_meas
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htpos : 0 < t := ht
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
          (div_nonneg (Real.exp_pos _).le htpos.le))]
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc
          |Real.sin t| * (Real.exp (-a * t) / t) ≤
              t * (Real.exp (-a * t) / t) := by
            gcongr
            simpa [abs_of_pos htpos] using Real.abs_sin_le_abs (x := t)
          _ = Real.exp (-a * t) := by field_simp
      apply hg_int.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := ht
      have hcalc :
          (∫ s : Real in Ioi a,
            ‖Real.exp (-s * t) * Real.sin t‖) = g t := by
        rw [show (fun s : Real => ‖Real.exp (-s * t) * Real.sin t‖) =
            fun s : Real => |Real.sin t| * Real.exp ((-t) * s) by
          funext s
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          rw [show -s * t = (-t) * s by ring]
          ring]
        rw [integral_const_mul]
        rw [integral_exp_mul_Ioi (neg_neg_of_pos htpos) a]
        dsimp [g]
        field_simp
      exact hcalc.symm
  · exact (Real.continuous_exp.comp
      (continuous_fst.neg.mul continuous_snd)).mul
        (Real.continuous_sin.comp continuous_snd) |>.aestronglyMeasurable

private theorem integral_damped_sinc_Ioi {a : Real} (ha : 0 < a) :
    (∫ t : Real in Ioi 0, Real.exp (-a * t) * Real.sinc t) =
      Real.pi / 2 - Real.arctan a := by
  have hprod : Integrable
      (Function.uncurry
        (fun s t : Real => Real.exp (-s * t) * Real.sin t))
      ((volume.restrict (Ioi a)).prod (volume.restrict (Ioi 0))) := by
    change Integrable
      (fun p : Real × Real => Real.exp (-p.1 * p.2) * Real.sin p.2)
      ((volume.restrict (Ioi a)).prod (volume.restrict (Ioi 0)))
    exact integrable_damped_sine_product ha
  have hswap := integral_integral_swap hprod
  have hleft :
      (∫ s : Real in Ioi a,
        ∫ t : Real in Ioi 0, Real.exp (-s * t) * Real.sin t) =
        ∫ s : Real in Ioi a, 1 / (s ^ 2 + 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact integral_exp_sin_Ioi (ha.trans hs)
  have hright :
      (∫ t : Real in Ioi 0,
        ∫ s : Real in Ioi a, Real.exp (-s * t) * Real.sin t) =
        ∫ t : Real in Ioi 0, Real.exp (-a * t) * Real.sinc t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := ht
    change (∫ s : Real in Ioi a, Real.exp (-s * t) * Real.sin t) =
      Real.exp (-a * t) * Real.sinc t
    rw [show (fun s : Real => Real.exp (-s * t) * Real.sin t) =
        fun s : Real => Real.exp ((-t) * s) * Real.sin t by
      funext s
      rw [show -s * t = (-t) * s by ring]]
    rw [integral_mul_const]
    rw [integral_exp_mul_Ioi (neg_neg_of_pos htpos) a]
    rw [Real.sinc_of_ne_zero htpos.ne']
    field_simp
  rw [hleft, hright] at hswap
  rw [show (fun s : Real => 1 / (s ^ 2 + 1)) =
      fun s : Real => (1 + s ^ 2)⁻¹ by
    funext s
    rw [one_div]
    congr 1
    ring] at hswap
  rw [integral_Ioi_inv_one_add_sq] at hswap
  exact hswap.symm

private theorem sinc_primitive_bound {L : Real}
    (hlim : Tendsto
      (fun R : Real => ∫ t in (0 : Real)..R, Real.sinc t)
      atTop (𝓝 L)) :
    ∃ C : Real, 0 < C ∧ ∀ t : Real, 0 ≤ t →
      |(∫ x in (0 : Real)..t, Real.sinc x)| ≤ C := by
  let F : Real → Real := fun R => ∫ t in (0 : Real)..R, Real.sinc t
  have hevent : ∀ᶠ t in atTop, |F t| < |L| + 1 := by
    exact hlim.abs.eventually (Iio_mem_nhds (by linarith [abs_nonneg L]))
  rw [eventually_atTop] at hevent
  obtain ⟨T, hT⟩ := hevent
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (intervalIntegral.integral_hasDerivAt_right
      (Real.continuous_sinc.intervalIntegrable (0 : Real) t)
      Real.continuous_sinc.stronglyMeasurable.stronglyMeasurableAtFilter
      Real.continuous_sinc.continuousAt).continuousAt
  have hcompact : Bornology.IsBounded (F '' Icc 0 (max 0 T)) :=
    (isCompact_Icc.image_of_continuousOn hFcont.continuousOn).isBounded
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_norm_le
  refine ⟨|C₀| + |L| + 1, by positivity, ?_⟩
  intro t ht
  by_cases htle : t ≤ max 0 T
  · have htmem : F t ∈ F '' Icc 0 (max 0 T) := ⟨t, ⟨ht, htle⟩, rfl⟩
    rw [← Real.norm_eq_abs]
    exact (hC₀ (F t) htmem).trans (by
      linarith [le_abs_self C₀, abs_nonneg L])
  · have hTt : T ≤ t :=
      (le_max_right 0 T).trans (le_of_not_ge htle)
    exact (hT t hTt).le.trans (by linarith [abs_nonneg C₀])

private theorem damped_sinc_eq_primitive_laplace {L a : Real}
    (hlim : Tendsto
      (fun R : Real => ∫ t in (0 : Real)..R, Real.sinc t)
      atTop (𝓝 L)) (ha : 0 < a) :
    (∫ t : Real in Ioi 0, Real.exp (-a * t) * Real.sinc t) =
      a * (∫ t : Real in Ioi 0,
        Real.exp (-a * t) *
          (∫ x in (0 : Real)..t, Real.sinc x)) := by
  let F : Real → Real := fun R => ∫ t in (0 : Real)..R, Real.sinc t
  have hFderiv (t : Real) : HasDerivAt F (Real.sinc t) t := by
    exact intervalIntegral.integral_hasDerivAt_right
      (Real.continuous_sinc.intervalIntegrable (0 : Real) t)
      Real.continuous_sinc.stronglyMeasurable.stronglyMeasurableAtFilter
      Real.continuous_sinc.continuousAt
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    exact fun t => (hFderiv t).continuousAt
  obtain ⟨C, hCpos, hC⟩ := sinc_primitive_bound hlim
  have hexp : IntegrableOn (fun t : Real => Real.exp (-a * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 ha
  have hFexp : IntegrableOn
      (fun t : Real => F t * Real.exp (-a * t)) (Ioi 0) := by
    apply MeasureTheory.Integrable.mono (hexp.const_mul C)
    · exact (hFcont.aestronglyMeasurable.mul
        ((Real.continuous_exp.comp
          (continuous_const.neg.mul continuous_id)).aestronglyMeasurable)).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hCpos,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hC t ht.le) (Real.exp_pos _).le
  have hsincV : IntegrableOn
      (fun t : Real => Real.sinc t *
        (-Real.exp (-a * t) / a)) (Ioi 0) := by
    apply MeasureTheory.Integrable.mono (hexp.const_mul (1 / a))
    · have hm : Measurable (fun t : Real => Real.sinc t *
          (-Real.exp (-a * t) / a)) := by
        fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_neg,
        abs_of_pos (Real.exp_pos _), abs_of_pos ha,
        abs_of_pos (by positivity : 0 < 1 / a)]
      have hsinc := Real.abs_sinc_le_one t
      calc
        |Real.sinc t| * (Real.exp (-a * t) / a) ≤
            1 * (Real.exp (-a * t) / a) := by gcongr
        _ = (1 / a) * Real.exp (-a * t) := by ring
  have hvderiv (t : Real) : HasDerivAt
      (fun x : Real => -Real.exp (-a * x) / a)
      (Real.exp (-a * t)) t := by
    simpa [ha.ne'] using
      ((hasDerivAt_id t).const_mul a).neg.exp.neg.div_const a
  have hzero : Tendsto
      (F * fun t : Real => -Real.exp (-a * t) / a)
      (𝓝[>] (0 : Real)) (𝓝 0) := by
    have hvcont : ContinuousAt
        (fun t : Real => -Real.exp (-a * t) / a) 0 := by fun_prop
    have hprod : Tendsto
        (F * fun t : Real => -Real.exp (-a * t) / a)
        (𝓝 (0 : Real)) (𝓝 0) := by
      have hvalue :
          (F * fun t : Real => -Real.exp (-a * t) / a) 0 = 0 := by
        simp [F]
      have hc := hFcont.continuousAt.mul hvcont
      change Tendsto
        (F * fun t : Real => -Real.exp (-a * t) / a)
        (𝓝 (0 : Real))
        (𝓝 ((F * fun t : Real => -Real.exp (-a * t) / a) 0)) at hc
      rw [hvalue] at hc
      exact hc
    exact hprod.mono_left inf_le_left
  have hvlim : Tendsto (fun t : Real => -Real.exp (-a * t) / a)
      atTop (𝓝 0) := by
    have harg : Tendsto (fun t : Real => -a * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha)
    have he : Tendsto (fun t : Real => Real.exp (-a * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    simpa using he.neg.div_const a
  have hinfty : Tendsto
      (F * fun t : Real => -Real.exp (-a * t) / a)
      atTop (𝓝 0) := by
    change Tendsto (fun t : Real => F t * (-Real.exp (-a * t) / a))
      atTop (𝓝 0)
    simpa [F] using hlim.mul hvlim
  have hip := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : Real)) (u := F) (u' := Real.sinc)
    (v := fun t : Real => -Real.exp (-a * t) / a)
    (v' := fun t : Real => Real.exp (-a * t))
    (fun t _ => hFderiv t) (fun t _ => hvderiv t)
    hFexp hsincV hzero hinfty
  have hsimpl :
      (∫ t : Real in Ioi 0,
        Real.sinc t * (-Real.exp (-a * t) / a)) =
        -(1 / a) *
          (∫ t : Real in Ioi 0,
            Real.exp (-a * t) * Real.sinc t) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  rw [hsimpl] at hip
  change (∫ t : Real in Ioi 0, Real.exp (-a * t) * Real.sinc t) =
    a * (∫ t : Real in Ioi 0, Real.exp (-a * t) * F t)
  have hcomm :
      (∫ t : Real in Ioi 0, F t * Real.exp (-a * t)) =
        ∫ t : Real in Ioi 0, Real.exp (-a * t) * F t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  rw [hcomm] at hip
  have ha0 : a ≠ 0 := ha.ne'
  simp only [sub_zero, zero_sub, neg_mul, neg_neg] at hip
  field_simp [ha0] at hip
  simpa only [neg_mul] using hip.symm

private theorem damped_sinc_eq_scaled_primitive {L a : Real}
    (hlim : Tendsto
      (fun R : Real => ∫ t in (0 : Real)..R, Real.sinc t)
      atTop (𝓝 L)) (ha : 0 < a) :
    (∫ t : Real in Ioi 0, Real.exp (-a * t) * Real.sinc t) =
      ∫ u : Real in Ioi 0, Real.exp (-u) *
        (∫ x in (0 : Real)..u / a, Real.sinc x) := by
  let F : Real → Real := fun R => ∫ t in (0 : Real)..R, Real.sinc t
  have hlaplace := damped_sinc_eq_primitive_laplace hlim ha
  have hchange := integral_comp_mul_left_Ioi
    (fun u : Real => Real.exp (-u) * F (u / a)) 0 ha
  have hleft :
      (∫ t : Real in Ioi 0,
        (fun u : Real => Real.exp (-u) * F (u / a)) (a * t)) =
        ∫ t : Real in Ioi 0, Real.exp (-a * t) * F t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change Real.exp (-(a * t)) * F (a * t / a) =
      Real.exp (-a * t) * F t
    rw [show a * t / a = t by field_simp [ha.ne']]
    congr 2
    ring
  simp only [mul_zero] at hchange
  rw [hleft] at hchange
  change (∫ t : Real in Ioi 0, Real.exp (-a * t) * Real.sinc t) =
    ∫ u : Real in Ioi 0, Real.exp (-u) * F (u / a)
  rw [hlaplace]
  rw [hchange]
  simp [ha.ne']

private theorem scaled_sinc_primitive_tendsto {L : Real}
    (hlim : Tendsto
      (fun R : Real => ∫ t in (0 : Real)..R, Real.sinc t)
      atTop (𝓝 L)) :
    Tendsto
      (fun n : Nat => ∫ u : Real in Ioi 0, Real.exp (-u) *
        (∫ x in (0 : Real)..u * ((n : Real) + 1), Real.sinc x))
      atTop (𝓝 L) := by
  let F : Real → Real := fun R => ∫ t in (0 : Real)..R, Real.sinc t
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (intervalIntegral.integral_hasDerivAt_right
      (Real.continuous_sinc.intervalIntegrable (0 : Real) t)
      Real.continuous_sinc.stronglyMeasurable.stronglyMeasurableAtFilter
      Real.continuous_sinc.continuousAt).continuousAt
  obtain ⟨C, hCpos, hC⟩ := sinc_primitive_bound hlim
  have hboundInt : Integrable
      (fun u : Real => C * Real.exp (-u)) (volume.restrict (Ioi 0)) := by
    simpa only [one_mul, neg_mul] using
      (exp_neg_integrableOn_Ioi 0 (b := (1 : Real)) (by norm_num)).const_mul C
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (μ := volume.restrict (Ioi 0))
    (F := fun (n : Nat) (u : Real) =>
      Real.exp (-u) * F (u * ((n : Real) + 1)))
    (f := fun u : Real => Real.exp (-u) * L)
    (fun u : Real => C * Real.exp (-u))
    (by
      filter_upwards [] with n
      have hm : Measurable (fun u : Real =>
          Real.exp (-u) * F (u * ((n : Real) + 1))) := by
        exact (Real.continuous_exp.comp continuous_id.neg).measurable.mul
          (hFcont.comp (continuous_id.mul continuous_const)).measurable
      exact hm.aestronglyMeasurable)
    (by
      filter_upwards [] with n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hnnonneg : 0 ≤ (n : Real) + 1 := by positivity
      have harg : 0 ≤ u * ((n : Real) + 1) :=
        mul_nonneg hu.le hnnonneg
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-u) * |F (u * ((n : Real) + 1))| ≤
            Real.exp (-u) * C := by
          gcongr
          exact hC _ harg
        _ = C * Real.exp (-u) := by ring)
    hboundInt
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hnat : Tendsto (fun n : Nat => (n : Real) + 1)
          atTop atTop :=
        tendsto_atTop_add_const_right atTop 1
          tendsto_natCast_atTop_atTop
      have harg : Tendsto (fun n : Nat => u * ((n : Real) + 1))
          atTop atTop := hnat.const_mul_atTop hu
      exact tendsto_const_nhds.mul (hlim.comp harg))
  have hlimitIntegral :
      (∫ u : Real in Ioi 0, Real.exp (-u) * L) = L := by
    rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]
  rw [hlimitIntegral] at hdct
  exact hdct

private theorem sinc_limit_eq_pi_div_two {L : Real}
    (hlim : Tendsto
      (fun R : Real => ∫ t in (0 : Real)..R, Real.sinc t)
      atTop (𝓝 L)) :
    L = Real.pi / 2 := by
  have hscaled := scaled_sinc_primitive_tendsto hlim
  have hseqeq (n : Nat) :
      (∫ t : Real in Ioi 0,
        Real.exp (-(1 / ((n : Real) + 1)) * t) * Real.sinc t) =
        ∫ u : Real in Ioi 0, Real.exp (-u) *
          (∫ x in (0 : Real)..u * ((n : Real) + 1), Real.sinc x) := by
    have hapos : 0 < 1 / ((n : Real) + 1) := by positivity
    have hs := damped_sinc_eq_scaled_primitive hlim hapos
    rw [hs]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    field_simp
  have hJtoL : Tendsto
      (fun n : Nat => ∫ t : Real in Ioi 0,
        Real.exp (-(1 / ((n : Real) + 1)) * t) * Real.sinc t)
      atTop (𝓝 L) := by
    apply hscaled.congr'
    exact Eventually.of_forall (fun n => (hseqeq n).symm)
  have hnat : Tendsto (fun n : Nat => (n : Real) + 1)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ha0 : Tendsto (fun n : Nat => 1 / ((n : Real) + 1))
      atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp hnat
  have harctan : Tendsto
      (fun n : Nat => Real.arctan (1 / ((n : Real) + 1)))
      atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def, Real.arctan_zero] using
      Real.continuous_arctan.continuousAt.tendsto.comp ha0
  have hformula : Tendsto
      (fun n : Nat => Real.pi / 2 -
        Real.arctan (1 / ((n : Real) + 1)))
      atTop (𝓝 (Real.pi / 2)) := by
    simpa using tendsto_const_nhds.sub harctan
  have hJtoPi : Tendsto
      (fun n : Nat => ∫ t : Real in Ioi 0,
        Real.exp (-(1 / ((n : Real) + 1)) * t) * Real.sinc t)
      atTop (𝓝 (Real.pi / 2)) := by
    apply hformula.congr'
    exact Eventually.of_forall (fun n =>
      (integral_damped_sinc_Ioi (by positivity :
        0 < 1 / ((n : Real) + 1))).symm)
  exact tendsto_nhds_unique hJtoL hJtoPi

private theorem integrable_cosine_tail_tenth :
    IntegrableOn (fun t : Real => Real.cos t / t ^ 10) (Ioi 1) := by
  have hmajor : IntegrableOn (fun t : Real => t ^ (-10 : Real)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  apply hmajor.mono'
  · exact (Real.continuous_cos.aemeasurable.div
      (continuous_id.pow 10).aemeasurable).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos htpos 10)]
    rw [show t ^ (-10 : Real) = 1 / t ^ 10 by
      norm_num [Real.rpow_neg_ofNat, zpow_neg]
      rfl]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one t)
      (pow_nonneg htpos.le 10)

private theorem exists_sinc_primitive_limit :
    ∃ L : Real, Tendsto
      (fun R : Real => ∫ t in (0 : Real)..R, Real.sinc t)
      atTop (𝓝 L) := by
  let tailLimit : Real :=
    0 - suzukiDF6D4SineTailPrimitive 1 -
      362880 * (∫ t : Real in Ioi 1, Real.cos t / t ^ 10)
  have hrem := intervalIntegral_tendsto_integral_Ioi 1
    integrable_cosine_tail_tenth tendsto_id
  have hformula : Tendsto
      (fun R : Real =>
        suzukiDF6D4SineTailPrimitive R -
          suzukiDF6D4SineTailPrimitive 1 -
            362880 * (∫ t in (1 : Real)..R, Real.cos t / t ^ 10))
      atTop (𝓝 tailLimit) := by
    unfold tailLimit
    exact (tendsto_suzukiDF6D4SineTailPrimitive_atTop.sub_const _).sub
      (hrem.const_mul 362880)
  have htail : Tendsto
      (fun R : Real => ∫ t in (1 : Real)..R, Real.sinc t)
      atTop (𝓝 tailLimit) := by
    apply hformula.congr'
    filter_upwards [eventually_ge_atTop (1 : Real)] with R hR
    exact (integral_sinc_tail_eq_primitive_sub (by norm_num) hR).symm
  let L : Real := (∫ t in (0 : Real)..1, Real.sinc t) + tailLimit
  refine ⟨L, ?_⟩
  have hconst : Tendsto
      (fun _ : Real => ∫ t in (0 : Real)..1, Real.sinc t)
      atTop (𝓝 (∫ t in (0 : Real)..1, Real.sinc t)) :=
    tendsto_const_nhds
  have hsum : Tendsto
      (fun R : Real => (∫ t in (0 : Real)..1, Real.sinc t) +
        ∫ t in (1 : Real)..R, Real.sinc t)
      atTop (𝓝 L) := by
    unfold L
    exact hconst.add htail
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : Real)] with R hR
  have hleft := Real.continuous_sinc.intervalIntegrable
    (μ := volume) (0 : Real) 1
  have hright := Real.continuous_sinc.intervalIntegrable
    (μ := volume) (1 : Real) R
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  exact hadd

theorem suzukiDirichletIntegralSource : SuzukiDirichletIntegralSource := by
  obtain ⟨L, hL⟩ := exists_sinc_primitive_limit
  have hvalue := sinc_limit_eq_pi_div_two hL
  simpa [SuzukiDirichletIntegralSource, hvalue] using hL

theorem suzukiDF6D4ComparisonSineTail_eq_pi_div_two_sub_integral'
    (mode : Nat) (hmode : 1 ≤ mode) :
    suzukiDF6D4ComparisonSineTail mode =
      Real.pi / 2 -
        ∫ t in (0 : Real)..suzukiDF6D4ComparisonWave mode, Real.sinc t :=
  suzukiDF6D4ComparisonSineTail_eq_pi_div_two_sub_integral
    suzukiDirichletIntegralSource mode hmode

theorem suzukiDF6D4SingularSineIntegral_eq_comparisonSineIntegral'
    (mode : Nat) (hmode : 1 ≤ mode) :
    2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      (1 / (2 * t)) *
        Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
      suzukiDF6D4ComparisonSineIntegral mode :=
  suzukiDF6D4SingularSineIntegral_eq_comparisonSineIntegral
    suzukiDirichletIntegralSource mode hmode

theorem suzukiDF6D4ComparisonSineTransform_normalization'
    (mode : Nat) (hmode : 1 ≤ mode) :
    suzukiDF6D4ComparisonSineTransform mode =
      -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (1 / (2 * t)) *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) :=
  suzukiDF6D4ComparisonSineTransform_normalization
    suzukiDirichletIntegralSource mode hmode

theorem suzukiDF6D4ArchimedeanIdentity
    (mode : Nat) (hmode : 1 ≤ mode) :
    -((Complex.digamma
        ((1 / 4 : Complex) +
          (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
            Complex.I)).im -
        ∑' k : Nat, suzukiDF6D4RestorationTerm mode k) -
        suzukiDF6D4ComparisonSineTransform mode =
      -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiR1SecondKernel t *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) :=
  suzukiDF6D4ArchimedeanIdentity_of_dirichletIntegral
    suzukiDirichletIntegralSource mode hmode

theorem suzukiDF6D4SmoothTransformDifference_eq_integral
    (mode : Nat) (hmode : 1 ≤ mode) :
    suzukiDF6D4SmoothTransformDifference mode =
      -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiRSecondKernel t *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) :=
  suzukiDF6D4SmoothTransformDifference_eq_integral_of_archimedean mode
    (suzukiDF6D4ArchimedeanIdentity mode hmode)

theorem suzukiDF6D4SmoothTransformDifference_abs_le
    (mode : Nat) (hmode : 1 ≤ mode) :
    |suzukiDF6D4SmoothTransformDifference mode| ≤
      (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
        Real.pi) / mode :=
  suzukiDF6D4SmoothTransformDifference_abs_le_of_archimedean mode hmode
    (suzukiDF6D4ArchimedeanIdentity mode hmode)

/-- The complete sine transform obeys the frozen mode-601 tail bound without
any remaining source-theorem premise. -/
theorem suzukiDF6D4CompleteSineTransform_abs_le_frozen
    (mode : Nat) (hmode : 601 ≤ mode) :
    |suzukiDF6D4CompleteSineTransform mode| ≤
      Real.pi / 2 + 1 / (Real.pi * 601) +
        Real.sqrt 2 * Real.log 2 +
          (2 * suzukiDF6D4RemainderVariationUpper * suzukiProjectAStar /
            Real.pi) / 601 :=
  suzukiDF6D4CompleteSineTransform_abs_le_frozen_of_smoothVariation
    mode hmode
    (suzukiDF6D4SmoothTransformDifference_abs_le mode (by omega))

end

end RiemannHypothesisProject.Experiments.M100
