import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.SuccPred.IntervalSucc
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.BinetSawtooth
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.KernelNormalization

/-!
# Laplace normalization of the Binet kernel

This module identifies the production Binet kernel with the Laplace transform
of the centered fractional-part function.  It then supplies the Fubini bridge
from the Euler-summation remainder to the Binet remainder.
-/

open Filter Function MeasureTheory Set Topology

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The centered sawtooth times a decaying exponential is integrable on the
positive half-line. -/
theorem integrableOn_binetSawtooth_mul_exp_neg
    {t : Real} (ht : 0 < t) :
    IntegrableOn (fun u : Real =>
      binetSawtooth u * Real.exp (-t * u)) (Set.Ioi 0) := by
  have hmaj : IntegrableOn (fun u : Real =>
      (1 / 2 : Real) * Real.exp (-t * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0).const_mul (1 / 2)
  refine hmaj.mono' ?_ ?_
  · exact (measurable_binetSawtooth.mul
      (Real.measurable_exp.comp
        (measurable_const.mul measurable_id))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (abs_binetSawtooth_le u)
      (Real.exp_pos _).le

/-- Exact Laplace integral of the centered sawtooth on one natural unit
interval. -/
theorem intervalIntegral_binetSawtooth_mul_exp_neg
    {t : Real} (ht : 0 < t) (n : Nat) :
    (∫ u in (n : Real)..(n + 1 : Real),
      binetSawtooth u * Real.exp (-t * u)) =
        Real.exp (-t * n) *
          ((1 + Real.exp (-t)) / (2 * t) -
            (1 - Real.exp (-t)) / t ^ 2) := by
  let q : Real → Real := fun u =>
    ((n : Real) + 1 / 2 - u) * Real.exp (-t * u)
  have hcongr :
      (∫ u in (n : Real)..(n + 1 : Real),
        binetSawtooth u * Real.exp (-t * u)) =
        ∫ u in (n : Real)..(n + 1 : Real), q u := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    change binetSawtooth u * Real.exp (-t * u) = q u
    rw [binetSawtooth_eq_on_nat_interval n hu]
  rw [hcongr]
  let A : Real → Real := fun u =>
    Real.exp (-t * u) *
      ((u - n - 1 / 2) / t + 1 / t ^ 2)
  have hderiv : ∀ u ∈ Set.uIcc (n : Real) (n + 1 : Real),
      HasDerivAt A (q u) u := by
    intro u _
    have hlinSource := (hasDerivAt_id u).const_mul (-t)
    have hlin : HasDerivAt (fun v : Real => -t * v) (-t) u := by
      refine (hlinSource.congr_deriv ?_).congr_of_eventuallyEq ?_
      · ring
      · filter_upwards with v
        simp only [id_eq]
    have hexp := hlin.exp
    have haff : HasDerivAt
        (fun v : Real => (v - n - 1 / 2) / t + 1 / t ^ 2)
        (1 / t) u := by
      have hnum := ((hasDerivAt_id u).sub_const (n : Real)).sub_const (1 / 2)
      have hdiv := hnum.div_const t
      have hadd := hdiv.add_const (1 / t ^ 2)
      refine (hadd.congr_deriv ?_).congr_of_eventuallyEq ?_
      · ring
      · filter_upwards with v
        rfl
    have hmain := hexp.mul haff
    refine (hmain.congr_deriv ?_).congr_of_eventuallyEq ?_
    · dsimp only [q]
      field_simp [ht.ne']
      ring
    · filter_upwards with v
      dsimp only [A]
      simp only [Pi.mul_apply]
  have hqInt : IntervalIntegrable q volume (n : Real) (n + 1 : Real) := by
    apply Continuous.intervalIntegrable
    unfold q
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hqInt]
  dsimp only [A]
  rw [show -t * ((n : Real) + 1) = -t * n + (-t) by ring,
    Real.exp_add]
  field_simp [ht.ne']
  ring

/-- The Laplace transform of the centered sawtooth is the elementary Binet
kernel divided by `t`. -/
theorem integral_binetSawtooth_mul_exp_neg
    {t : Real} (ht : 0 < t) :
    (∫ u : Real in Set.Ioi 0,
      binetSawtooth u * Real.exp (-t * u)) =
        (1 - Real.exp (-t))⁻¹ *
          ((1 + Real.exp (-t)) / (2 * t) -
            (1 - Real.exp (-t)) / t ^ 2) := by
  let f : Real → Real := fun u =>
    binetSawtooth u * Real.exp (-t * u)
  have hunion :
      (⋃ n : Nat, Set.Ioc (n : Real) (n + 1 : Real)) = Set.Ioi 0 := by
    have hnonneg : ∀ n : Nat, (0 : Real) ≤ n := Nat.cast_nonneg
    have hunbounded : ¬ BddAbove (Set.range fun n : Nat => (n : Real)) := by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := exists_nat_gt a
      exact (not_lt_of_ge (ha ⟨n, rfl⟩)) hn
    simpa only [Nat.cast_zero, Nat.cast_succ] using
      (show (⋃ n : Nat,
          Set.Ioc ((fun m : Nat => (m : Real)) n)
            ((fun m : Nat => (m : Real)) (Nat.succ n))) =
            Set.Ioi ((fun m : Nat => (m : Real)) 0) from
        iUnion_Ioc_map_succ_eq_Ioi
        (f := fun n : Nat => (n : Real))
        (fun n => by simpa using hnonneg n) hunbounded)
  have hdisjoint : Pairwise (Disjoint on
      fun n : Nat => Set.Ioc (n : Real) (n + 1 : Real)) := by
    have hmono : Monotone (fun n : Nat => (n : Real)) := fun _ _ h => by
      dsimp only
      exact_mod_cast h
    simpa only [Nat.cast_succ] using
      (show Pairwise (Disjoint on fun n : Nat =>
          Set.Ioc ((fun m : Nat => (m : Real)) n)
            ((fun m : Nat => (m : Real)) (Nat.succ n))) from
        hmono.pairwise_disjoint_on_Ioc_succ)
  have hsSet : HasSum
      (fun n : Nat => ∫ u in Set.Ioc (n : Real) (n + 1 : Real), f u)
      (∫ u in Set.Ioi 0, f u) := by
    have hs := hasSum_integral_iUnion
      (f := f) (s := fun n : Nat => Set.Ioc (n : Real) (n + 1 : Real))
      (fun _ => measurableSet_Ioc) hdisjoint
      (by rw [hunion]; exact integrableOn_binetSawtooth_mul_exp_neg ht)
    simpa only [hunion] using hs
  have hsInterval : HasSum
      (fun n : Nat => ∫ u in (n : Real)..(n + 1 : Real), f u)
      (∫ u in Set.Ioi 0, f u) := by
    apply HasSum.congr_fun hsSet
    intro n
    rw [intervalIntegral.integral_of_le (by norm_num)]
  let B : Real :=
    (1 + Real.exp (-t)) / (2 * t) -
      (1 - Real.exp (-t)) / t ^ 2
  have hsB : HasSum (fun n : Nat => Real.exp (-t * n) * B)
      (∫ u in Set.Ioi 0, f u) := by
    apply HasSum.congr_fun hsInterval
    intro n
    simpa only [f, B] using
      (intervalIntegral_binetSawtooth_mul_exp_neg ht n).symm
  let q : Real := Real.exp (-t)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp only [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : HasSum (fun n : Nat => Real.exp (-t * n) * B)
      ((1 - q)⁻¹ * B) := by
    have h := (hasSum_geometric_of_norm_lt_one
      (ξ := q) (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0])).mul_right B
    apply HasSum.congr_fun h
    intro n
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  have hunique := hsB.unique hgeom
  simpa only [f, B, q] using hunique

/-- Pointwise real normalization of the production Binet kernel. -/
theorem mul_integral_binetSawtooth_mul_exp_neg
    {t : Real} (ht : 0 < t) :
    t * (∫ u : Real in Set.Ioi 0,
      binetSawtooth u * Real.exp (-t * u)) =
        (1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1) := by
  rw [integral_binetSawtooth_mul_exp_neg ht]
  have ht0 : t ≠ 0 := ht.ne'
  have he0 : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have he1 : Real.exp t - 1 ≠ 0 :=
    sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr ht).ne'
  rw [Real.exp_neg]
  field_simp [ht0, he0, he1]
  ring

/-- Complex-valued pointwise form matching the production kernel exactly. -/
theorem bennettGammaBinetKernel_eq_sawtoothLaplace
    {t : Real} (ht : 0 < t) :
    bennettGammaBinetKernel t =
      (t * (∫ u : Real in Set.Ioi 0,
        binetSawtooth u * Real.exp (-t * u)) : Real) := by
  rw [bennettGammaBinetKernel_eq_ofReal]
  exact_mod_cast (mul_integral_binetSawtooth_mul_exp_neg ht).symm

/-- The first exponential moment on the positive half-line is integrable. -/
theorem integrableOn_mul_exp_neg_mul
    {r : Real} (hr : 0 < r) :
    IntegrableOn (fun t : Real => t * Real.exp (-(r * t)))
      (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : Real)) (s := (1 : Real)) (b := r)
    (by norm_num) (by norm_num) hr
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  change t ^ (1 : Real) * Real.exp (-r * t ^ (1 : Real)) =
    t * Real.exp (-(r * t))
  rw [Real.rpow_one]
  congr 2
  ring

/-- Exact first exponential moment. -/
theorem integral_mul_exp_neg_mul
    {r : Real} (hr : 0 < r) :
    (∫ t : Real in Set.Ioi 0, t * Real.exp (-(r * t))) =
      1 / r ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : Real)) (r := r) (by norm_num) hr
  norm_num [Real.rpow_one] at h
  convert h using 1 <;> field_simp [hr.ne'] <;> ring

/-- A shifted reciprocal square is integrable on the positive half-line. -/
theorem integrableOn_one_div_add_sq
    {x : Real} (hx : 0 < x) :
    IntegrableOn (fun u : Real => 1 / (x + u) ^ 2) (Set.Ioi 0) := by
  have hbase := integrableOn_add_rpow_Ioi_of_lt
    (a := (-2 : Real)) (c := (0 : Real)) (m := x)
    (by norm_num) (by linarith)
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro u hu
  have hxu : 0 < x + u := by linarith [Set.mem_Ioi.mp hu]
  change (u + x) ^ (-2 : Real) = 1 / (x + u) ^ 2
  rw [show u + x = x + u by ring,
    show (-2 : Real) = -(2 : Real) by norm_num,
    Real.rpow_neg hxu.le, Real.rpow_two]
  simp only [one_div]

/-- Absolute integrability needed for the Binet/sawtooth Fubini swap. -/
theorem integrable_binetSawtooth_fubini
    {x : Real} (hx : 0 < x) :
    let μ := volume.restrict (Set.Ioi (0 : Real))
    Integrable (fun p : Real × Real =>
      binetSawtooth p.2 * p.1 *
        Real.exp (-(x + p.2) * p.1)) (μ.prod μ) := by
  let μ := volume.restrict (Set.Ioi (0 : Real))
  let F : Real × Real → Real := fun p =>
    binetSawtooth p.2 * p.1 * Real.exp (-(x + p.2) * p.1)
  have hmeas : AEStronglyMeasurable F (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    unfold F
    have hfst : Measurable (fun p : Real × Real => p.1) := measurable_fst
    have hsnd : Measurable (fun p : Real × Real => p.2) := measurable_snd
    exact (((measurable_binetSawtooth.comp hsnd).mul hfst).mul
      (Real.measurable_exp.comp ((measurable_const.add hsnd).neg.mul hfst)))
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hxu : 0 < x + u := by linarith [Set.mem_Ioi.mp hu]
    have h := (integrableOn_mul_exp_neg_mul hxu).const_mul
      (binetSawtooth u)
    simpa only [μ, F, mul_assoc, neg_mul] using h
  · have hmaj : Integrable (fun u : Real =>
        (1 / 2 : Real) * (1 / (x + u) ^ 2)) μ :=
      (integrableOn_one_div_add_sq hx).const_mul (1 / 2)
    refine hmaj.mono' ?_ ?_
    · have hm := hmeas.norm.prod_swap.integral_prod_right'
      simpa only [F, Function.comp_apply, Prod.swap_prod_mk, μ] using hm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hxu : 0 < x + u := by linarith [Set.mem_Ioi.mp hu]
      calc
        ‖∫ t, ‖F (t, u)‖ ∂μ‖ = (∫ t, ‖F (t, u)‖ ∂μ) := by
              rw [Real.norm_eq_abs, abs_of_nonneg]
              exact integral_nonneg fun _ => norm_nonneg _
        _ =
            |binetSawtooth u| *
              (∫ t : Real in Set.Ioi 0,
                t * Real.exp (-((x + u) * t))) := by
              rw [← MeasureTheory.integral_const_mul]
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              have ht0 := Set.mem_Ioi.mp ht
              simp only [F, Real.norm_eq_abs, abs_mul,
                abs_of_pos ht0, abs_of_pos (Real.exp_pos _), μ]
              ring
        _ = |binetSawtooth u| * (1 / (x + u) ^ 2) := by
          rw [integral_mul_exp_neg_mul hxu]
        _ ≤ (1 / 2 : Real) * (1 / (x + u) ^ 2) := by
          exact mul_le_mul_of_nonneg_right (abs_binetSawtooth_le u) (by positivity)

/-- The Laplace transform of the production real kernel equals the
Euler-summation sawtooth remainder. -/
theorem integral_binetKernelReal_mul_exp_neg
    {x : Real} (hx : 0 < x) :
    (∫ t : Real in Set.Ioi 0,
      ((1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1)) *
        Real.exp (-x * t)) =
      ∫ u : Real in Set.Ioi 0,
        binetSawtooth u / (x + u) ^ 2 := by
  let μ := volume.restrict (Set.Ioi (0 : Real))
  let F : Real × Real → Real := fun p =>
    binetSawtooth p.2 * p.1 * Real.exp (-(x + p.2) * p.1)
  have hF : Integrable F (μ.prod μ) := by
    simpa only [μ, F] using integrable_binetSawtooth_fubini hx
  have hswap :
      (∫ t, ∫ u, F (t, u) ∂μ ∂μ) =
        ∫ u, ∫ t, F (t, u) ∂μ ∂μ :=
    integral_integral_swap hF
  calc
    (∫ t : Real in Set.Ioi 0,
      ((1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1)) *
        Real.exp (-x * t)) =
        ∫ t : Real in Set.Ioi 0, ∫ u : Real in Set.Ioi 0, F (t, u) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          have ht0 := Set.mem_Ioi.mp ht
          change ((1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1)) *
              Real.exp (-x * t) = ∫ u : Real in Set.Ioi 0, F (t, u)
          rw [← mul_integral_binetSawtooth_mul_exp_neg ht0]
          calc
            (t * (∫ u : Real in Set.Ioi 0,
                binetSawtooth u * Real.exp (-t * u))) * Real.exp (-x * t) =
                (t * Real.exp (-x * t)) *
                  (∫ u : Real in Set.Ioi 0,
                    binetSawtooth u * Real.exp (-t * u)) := by ring
            _ = ∫ u : Real in Set.Ioi 0,
                (t * Real.exp (-x * t)) *
                  (binetSawtooth u * Real.exp (-t * u)) := by
                    rw [MeasureTheory.integral_const_mul]
            _ = ∫ u : Real in Set.Ioi 0, F (t, u) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro u _
              dsimp only [F]
              have hexp : Real.exp (-x * t) * Real.exp (-t * u) =
                  Real.exp (-(x + u) * t) := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [← hexp]
              ring
    _ = ∫ t, ∫ u, F (t, u) ∂μ ∂μ := rfl
    _ = ∫ u, ∫ t, F (t, u) ∂μ ∂μ := hswap
    _ = ∫ u : Real in Set.Ioi 0,
        binetSawtooth u / (x + u) ^ 2 := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          have hxu : 0 < x + u := by linarith [Set.mem_Ioi.mp hu]
          calc
            (∫ t : Real in Set.Ioi 0, F (t, u)) =
                binetSawtooth u *
                  (∫ t : Real in Set.Ioi 0,
                    t * Real.exp (-((x + u) * t))) := by
                      rw [← MeasureTheory.integral_const_mul]
                      apply setIntegral_congr_fun measurableSet_Ioi
                      intro t _
                      dsimp only [F]
                      ring
            _ = binetSawtooth u * (1 / (x + u) ^ 2) := by
              rw [integral_mul_exp_neg_mul hxu]
            _ = binetSawtooth u / (x + u) ^ 2 := by ring

/-- Complex form of the real Fubini identity on the positive real axis. -/
theorem integral_bennettGammaBinetKernel_ofReal
    {x : Real} (hx : 0 < x) :
    (∫ t : Real in Set.Ioi 0,
      bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * (x : Complex))) =
      ((∫ u : Real in Set.Ioi 0,
        binetSawtooth u / (x + u) ^ 2 : Real) : Complex) := by
  rw [← integral_binetKernelReal_mul_exp_neg hx]
  calc
    (∫ t : Real in Set.Ioi 0,
        bennettGammaBinetKernel t *
          Complex.exp (-(t : Complex) * (x : Complex))) =
        ∫ t : Real in Set.Ioi 0,
          ((((1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1)) *
            Real.exp (-x * t) : Real) : Complex) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [bennettGammaBinetKernel_eq_ofReal]
      have hexp : Complex.exp (-(t : Complex) * (x : Complex)) =
          (Real.exp (-x * t) : Complex) := by
        have harg : -(t : Complex) * (x : Complex) =
            ((-x * t : Real) : Complex) := by
          push_cast
          ring
        rw [harg, ← Complex.ofReal_exp]
      rw [hexp, ← Complex.ofReal_mul]
    _ = ((∫ t : Real in Set.Ioi 0,
          ((1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1)) *
            Real.exp (-x * t) : Real) : Complex) := integral_ofReal

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
