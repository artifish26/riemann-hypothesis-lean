import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.GaussDigammaHolomorphic

/-!
# Euler-summation form of the Binet remainder

This module introduces the centered fractional-part function used to connect
the production Binet kernel with the trapezoidal error for `u ↦ 1 / (x+u)`.
-/

open Filter MeasureTheory Set Topology

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The centered sawtooth in the sign convention whose Laplace transform is
the production Binet kernel divided by `t`. -/
def binetSawtooth (u : Real) : Real :=
  1 / 2 - Int.fract u

/-- The centered sawtooth is bounded in absolute value by `1/2`. -/
theorem abs_binetSawtooth_le (u : Real) :
    |binetSawtooth u| ≤ 1 / 2 := by
  rw [abs_le]
  constructor <;> unfold binetSawtooth <;>
    have h₀ := Int.fract_nonneg u <;>
    have h₁ := (Int.fract_lt_one u).le <;> linarith

/-- The centered sawtooth is measurable. -/
theorem measurable_binetSawtooth : Measurable binetSawtooth := by
  unfold binetSawtooth
  fun_prop

/-- On a unit interval based at a natural number, the fractional part is the
local coordinate. -/
theorem binetSawtooth_eq_on_nat_interval
    (n : Nat) {u : Real} (hu : u ∈ Set.Ioo (n : Real) (n + 1 : Real)) :
    binetSawtooth u = (n : Real) + 1 / 2 - u := by
  have hlocal : Int.fract (u - n) = u - n :=
    Int.fract_eq_self.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
  unfold binetSawtooth
  rw [← Int.fract_sub_natCast u n, hlocal]
  ring

/-- Exact single-interval Euler--trapezoid identity. -/
theorem intervalIntegral_binetSawtooth_div_sq
    {x : Real} (hx : 0 < x) (n : Nat) :
    (∫ u in (n : Real)..(n + 1 : Real),
      binetSawtooth u / (x + u) ^ 2) =
        (1 / 2 : Real) *
            (1 / (x + n) + 1 / (x + n + 1)) -
          (Real.log (x + n + 1) - Real.log (x + n)) := by
  let q : Real → Real := fun u =>
    ((n : Real) + 1 / 2 - u) / (x + u) ^ 2
  have hcongr :
      (∫ u in (n : Real)..(n + 1 : Real),
        binetSawtooth u / (x + u) ^ 2) =
        ∫ u in (n : Real)..(n + 1 : Real), q u := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    change binetSawtooth u / (x + u) ^ 2 = q u
    rw [binetSawtooth_eq_on_nat_interval n hu]
  rw [hcongr]
  let A : Real → Real := fun u =>
    -((x + n + 1 / 2) / (x + u)) - Real.log (x + u)
  have hderiv : ∀ u ∈ Set.uIcc (n : Real) (n + 1 : Real),
      HasDerivAt A (q u) u := by
    intro u hu
    have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
    have hu0 : 0 < x + u := by
      rw [Set.uIcc_of_le (by norm_num)] at hu
      linarith [hu.1]
    have hadd : HasDerivAt (fun v : Real => x + v) 1 u :=
      (hasDerivAt_id u).const_add x
    have hinv := hadd.inv hu0.ne'
    have hlog := (Real.hasDerivAt_log hu0.ne').comp u hadd
    have hmain := (hinv.const_mul (-(x + n + 1 / 2))).sub hlog
    refine (hmain.congr_deriv ?_).congr_of_eventuallyEq ?_
    · dsimp only [q]
      field_simp [hu0.ne']
      ring
    · filter_upwards with v
      dsimp only [A]
      simp only [Pi.sub_apply, Pi.inv_apply, Function.comp_apply]
      ring
  have hqInt : IntervalIntegrable q volume (n : Real) (n + 1 : Real) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    apply ContinuousAt.continuousWithinAt
    have hu0 : 0 < x + u := by
      rw [Set.uIcc_of_le (by norm_num)] at hu
      have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
      linarith [hu.1]
    unfold q
    fun_prop (disch := exact pow_ne_zero 2 hu0.ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hqInt]
  dsimp only [A]
  have hxn : x + (n : Real) ≠ 0 := by positivity
  have hxn1 : x + (n : Real) + 1 ≠ 0 := by positivity
  field_simp [hxn, hxn1]
  ring

/-- The sawtooth remainder is integrable on each natural unit interval. -/
theorem intervalIntegrable_binetSawtooth_div_sq_nat
    {x : Real} (hx : 0 < x) (n : Nat) :
    IntervalIntegrable (fun u : Real =>
      binetSawtooth u / (x + u) ^ 2) volume n (n + 1) := by
  let q : Real → Real := fun u =>
    ((n : Real) + 1 / 2 - u) / (x + u) ^ 2
  have hq : IntervalIntegrable q volume (n : Real) (n + 1 : Real) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    apply ContinuousAt.continuousWithinAt
    have hu0 : 0 < x + u := by
      rw [Set.uIcc_of_le (by norm_num)] at hu
      have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
      linarith [hu.1]
    unfold q
    fun_prop (disch := exact pow_ne_zero 2 hu0.ne')
  exact hq.congr_uIoo fun u hu => by
    rw [Set.uIoo_of_le (by norm_num)] at hu
    change q u = binetSawtooth u / (x + u) ^ 2
    rw [binetSawtooth_eq_on_nat_interval n hu]

/-- Finite Euler summation for the sawtooth remainder.  The last parenthesis
is the boundary term that vanishes at infinity. -/
theorem intervalIntegral_binetSawtooth_div_sq_zero_nat
    {x : Real} (hx : 0 < x) (N : Nat) :
    (∫ u in (0 : Real)..(N : Real),
      binetSawtooth u / (x + u) ^ 2) =
        Real.log x - deriv (Real.log ∘ Real.Gamma) x - 1 / (2 * x) +
          (deriv (Real.log ∘ Real.Gamma) (x + N) -
            Real.log (x + N) + 1 / (2 * (x + N))) := by
  let r : Nat → Real := fun n => 1 / (x + n)
  have hsumInt :
      (∫ u in (0 : Real)..(N : Real),
        binetSawtooth u / (x + u) ^ 2) =
        ∑ n ∈ Finset.range N,
          ∫ u in (n : Real)..(n + 1 : Real),
            binetSawtooth u / (x + u) ^ 2 := by
    symm
    simpa using intervalIntegral.sum_integral_adjacent_intervals
      (a := fun n : Nat => (n : Real))
      (f := fun u : Real => binetSawtooth u / (x + u) ^ 2)
      (μ := volume) (n := N)
      (fun n _ => by simpa only [Nat.cast_add, Nat.cast_one] using
        intervalIntegrable_binetSawtooth_div_sq_nat hx n)
  have hshift :
      (∑ n ∈ Finset.range N, r (n + 1)) =
        (∑ n ∈ Finset.range N, r n) - r 0 + r N := by
    have htel := Finset.sum_range_sub r N
    rw [Finset.sum_sub_distrib] at htel
    linarith
  have hlog :
      (∑ n ∈ Finset.range N,
        (Real.log (x + n + 1) - Real.log (x + n))) =
          Real.log (x + N) - Real.log x := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
      add_assoc] using
        (Finset.sum_range_sub (fun n : Nat => Real.log (x + n)) N)
  rw [hsumInt]
  simp_rw [intervalIntegral_binetSawtooth_div_sq hx]
  rw [Finset.sum_sub_distrib, hlog]
  have hrec := deriv_logGamma_add_nat hx N
  change deriv (Real.log ∘ Real.Gamma) (x + N) =
      deriv (Real.log ∘ Real.Gamma) x +
        ∑ n ∈ Finset.range N, r n at hrec
  have hshift' :
      (∑ n ∈ Finset.range N, 1 / (x + n + 1)) =
        (∑ n ∈ Finset.range N, 1 / (x + n)) - 1 / x +
          1 / (x + N) := by
    simpa only [r, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
      add_assoc] using hshift
  calc
    (∑ n ∈ Finset.range N,
        (1 / 2 : Real) *
          (1 / (x + n) + 1 / (x + n + 1))) -
          (Real.log (x + N) - Real.log x) =
        (1 / 2 : Real) *
            ((∑ n ∈ Finset.range N, 1 / (x + n)) +
              ∑ n ∈ Finset.range N, 1 / (x + n + 1)) -
          (Real.log (x + N) - Real.log x) := by
            simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = Real.log x - deriv (Real.log ∘ Real.Gamma) x - 1 / (2 * x) +
          (deriv (Real.log ∘ Real.Gamma) (x + N) -
            Real.log (x + N) + 1 / (2 * (x + N))) := by
            rw [hshift']
            dsimp only [r] at hrec
            rw [hrec]
            have hxN : x + (N : Real) ≠ 0 := by positivity
            field_simp [hx.ne', hxN]
            ring

/-- The Euler-summation remainder is absolutely integrable on the positive
half-line. -/
theorem integrableOn_binetSawtooth_div_sq
    {x : Real} (hx : 0 < x) :
    IntegrableOn (fun u : Real =>
      binetSawtooth u / (x + u) ^ 2) (Set.Ioi 0) := by
  have hinv : IntegrableOn (fun u : Real => 1 / (x + u) ^ 2)
      (Set.Ioi 0) := by
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
  have hmaj : IntegrableOn (fun u : Real =>
      (1 / 2 : Real) * (1 / (x + u) ^ 2)) (Set.Ioi 0) :=
    hinv.const_mul (1 / 2 : Real)
  refine hmaj.mono' ?_ ?_
  · exact (measurable_binetSawtooth.div
      ((measurable_const.add measurable_id).pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hxu : 0 < x + u := by linarith [Set.mem_Ioi.mp hu]
    have hsq : 0 < (x + u) ^ 2 := sq_pos_of_pos hxu
    calc
      ‖binetSawtooth u / (x + u) ^ 2‖ =
          |binetSawtooth u| / (x + u) ^ 2 := by
            rw [Real.norm_eq_abs, abs_div, abs_of_pos hsq]
      _ ≤ (1 / 2 : Real) / (x + u) ^ 2 :=
        div_le_div_of_nonneg_right (abs_binetSawtooth_le u) hsq.le
      _ = (1 / 2 : Real) * (1 / (x + u) ^ 2) := by ring

/-- Euler summation identifies the integral of the centered sawtooth with
the real Binet remainder. -/
theorem integral_binetSawtooth_div_sq
    {x : Real} (hx : 0 < x) :
    (∫ u : Real in Set.Ioi 0,
      binetSawtooth u / (x + u) ^ 2) =
        Real.log x - deriv (Real.log ∘ Real.Gamma) x - 1 / (2 * x) := by
  let C : Real :=
    Real.log x - deriv (Real.log ∘ Real.Gamma) x - 1 / (2 * x)
  have hlogShift :
      Tendsto (fun n : Nat =>
        Real.log (x + n) - Real.log n) atTop (nhds 0) := by
    have h := (Real.tendsto_log_comp_add_sub_log x).comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    funext n
    congr 2 <;> ring
  have hderiv :
      Tendsto (fun n : Nat =>
        deriv (Real.log ∘ Real.Gamma) (x + n) - Real.log (x + n))
        atTop (nhds 0) := by
    have h := (tendsto_deriv_logGamma_add_nat_sub_log hx).sub hlogShift
    convert h using 1
    · funext n
      ring
    · ring
  have hxTop : Tendsto (fun n : Nat => x + (n : Real)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : Nat => 1 / (2 * (x + n))) atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Tendsto
      (fun _ : Nat => (1 / 2 : Real)) atTop (nhds (1 / 2 : Real))).mul
        (tendsto_inv_atTop_zero.comp hxTop)
    simpa only [Function.comp_apply, one_div, mul_inv_rev, mul_zero,
      zero_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hboundary :
      Tendsto (fun n : Nat =>
        deriv (Real.log ∘ Real.Gamma) (x + n) - Real.log (x + n) +
          1 / (2 * (x + n))) atTop (nhds 0) := by
    simpa using hderiv.add hinv
  have hrhs :
      Tendsto (fun n : Nat => C +
        (deriv (Real.log ∘ Real.Gamma) (x + n) - Real.log (x + n) +
          1 / (2 * (x + n)))) atTop (nhds C) := by
    simpa using (tendsto_const_nhds.add hboundary)
  have hfinite :
      Tendsto (fun n : Nat =>
        ∫ u in (0 : Real)..(n : Real),
          binetSawtooth u / (x + u) ^ 2) atTop (nhds C) := by
    apply hrhs.congr'
    filter_upwards [] with n
    exact (intervalIntegral_binetSawtooth_div_sq_zero_nat hx n).symm
  have himproper := intervalIntegral_tendsto_integral_Ioi
    (f := fun u : Real => binetSawtooth u / (x + u) ^ 2)
    (μ := volume) (b := fun n : Nat => (n : Real)) (l := atTop)
    0 (integrableOn_binetSawtooth_div_sq hx) tendsto_natCast_atTop_atTop
  exact tendsto_nhds_unique himproper hfinite

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
