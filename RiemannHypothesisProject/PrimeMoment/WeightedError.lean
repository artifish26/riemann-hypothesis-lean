import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Asymptotics
import RiemannHypothesisProject.PrimeMoment.PartialSummation

/-!
# Weighted PNT error for the Li prime moments

The pinned PNT remainder has stretched-exponential decay in `log x`.  This
module proves the two consequences needed after finite partial summation:
global integrability of the weighted error and decay of its endpoint term.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Asymptotics Filter MeasureTheory
open scoped Chebyshev Topology

/-- Positive stretched exponentials dominate every real power at infinity,
and are integrable at the origin whenever the power is locally integrable. -/
theorem integrableOn_rpow_mul_exp_neg_mul_rpow_of_pos
    {s p c : Real} (hs : -1 < s) (hp : 0 < p) (hc : 0 < c) :
    IntegrableOn (fun x : Real => x ^ s * Real.exp (-c * x ^ p))
      (Set.Ioi 0) := by
  let q : Real := p⁻¹
  let r : Real := q * (s + 1) - 1
  have hq : 0 < q := by simpa [q] using inv_pos.mpr hp
  have hr : -1 < r := by
    dsimp [r]
    nlinarith [mul_pos hq (by linarith : 0 < s + 1)]
  have hbase : IntegrableOn
      (fun x : Real => x ^ r * Real.exp (-c * x ^ (1 : Real)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hr le_rfl hc
  have htrans : IntegrableOn
      (fun x : Real => (|q| * x ^ (q - 1)) •
        ((x ^ q) ^ s * Real.exp (-c * (x ^ q) ^ p)))
      (Set.Ioi 0) := by
    have hscaled : IntegrableOn
        (fun x : Real => q * (x ^ r * Real.exp (-c * x ^ (1 : Real))))
        (Set.Ioi 0) := hbase.const_mul q
    apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    simp only [smul_eq_mul, abs_of_pos hq]
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]
    have hqp : q * p = 1 := by
      dsimp [q]
      exact inv_mul_cancel₀ hp.ne'
    symm
    calc
      q * x ^ (q - 1) *
          (x ^ (q * s) * Real.exp (-c * x ^ (q * p))) =
          q * (x ^ ((q - 1) + q * s) *
            Real.exp (-c * x ^ (q * p))) := by
            rw [Real.rpow_add hx0]
            ring
      _ = q * (x ^ r * Real.exp (-c * x ^ (1 : Real))) := by
        rw [hqp]
        congr 2
        dsimp [r]
        ring
  exact (integrableOn_Ioi_comp_rpow_iff
    (fun x : Real => x ^ s * Real.exp (-c * x ^ p)) hq.ne').mp htrans

/-- Logarithmic transport of the positive stretched-exponential integral. -/
theorem integrableOn_log_rpow_div_mul_exp_neg_mul_log_rpow
    {s p c : Real} (hs : -1 < s) (hp : 0 < p) (hc : 0 < c) :
    IntegrableOn
      (fun x : Real => Real.log x ^ s / x *
        Real.exp (-c * Real.log x ^ p)) (Set.Ioi 1) := by
  let g : Real → Real := fun x => Real.log x ^ s / x *
    Real.exp (-c * Real.log x ^ p)
  have himage : Real.exp '' Set.Ioi (0 : Real) = Set.Ioi 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using (Real.exp_lt_exp.mpr hx)
    · intro hy
      have hy' : 1 < y := hy
      refine ⟨Real.log y, Real.log_pos hy', ?_⟩
      exact Real.exp_log (zero_lt_one.trans hy')
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Ioi (0 : Real)) (f := Real.exp) (f' := Real.exp)
    measurableSet_Ioi
    (fun x hx => Real.hasDerivAt_exp x |>.hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [himage] at hiff
  apply hiff.mpr
  apply IntegrableOn.congr_fun
    (integrableOn_rpow_mul_exp_neg_mul_rpow_of_pos hs hp hc) _
    measurableSet_Ioi
  intro x hx
  simp only [g, abs_of_pos (Real.exp_pos x), smul_eq_mul, Real.log_exp]
  field_simp [Real.exp_ne_zero]

theorem integrableOn_log_pow_div_mul_exp_neg_mul_log_rpow
    (j : Nat) {p c : Real} (hp : 0 < p) (hc : 0 < c) :
    IntegrableOn
      (fun x : Real => Real.log x ^ j / x *
        Real.exp (-c * Real.log x ^ p)) (Set.Ioi 1) := by
  apply IntegrableOn.congr_fun
    (integrableOn_log_rpow_div_mul_exp_neg_mul_log_rpow
      (s := (j : Real))
        (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg j)) hp hc) _
    measurableSet_Ioi
  intro x hx
  simp only [Real.rpow_natCast]

theorem continuousOn_deriv_liPrimeMomentWeight_Ici (j : Nat) :
    ContinuousOn (deriv (liPrimeMomentWeight j)) (Set.Ici (1 : Real)) := by
  have hcontinuous : ContinuousOn (liPrimeMomentWeightDeriv j)
      (Set.Ici (1 : Real)) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le hx)
    exact (((continuousAt_const.mul
      ((Real.continuousAt_log hx0).pow (j - 1))).sub
        ((Real.continuousAt_log hx0).pow j)).div
          (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).continuousWithinAt
  refine hcontinuous.congr ?_
  intro x hx
  exact deriv_liPrimeMomentWeight j
    (ne_of_gt (zero_lt_one.trans_le hx))

theorem locallyIntegrableOn_weighted_liPrimeMomentPNTError (j : Nat) :
    LocallyIntegrableOn
      (fun x => deriv (liPrimeMomentWeight j) x * liPrimeMomentPNTError x)
      (Set.Ici (1 : Real)) := by
  have herror : LocallyIntegrableOn liPrimeMomentPNTError
      (Set.Ici (1 : Real)) := by
    exact ((Chebyshev.psi_mono.locallyIntegrable.sub
      continuous_id.locallyIntegrable).locallyIntegrableOn _).congr
        (Filter.Eventually.of_forall fun x => by rfl)
  exact herror.continuousOn_mul
    (continuousOn_deriv_liPrimeMomentWeight_Ici j)
    isClosed_Ici.isLocallyClosed

theorem integrableOn_deriv_liPrimeMomentWeight_mul_pntMajorant
    (j : Nat) {c : Real} (hc : 0 < c) :
    IntegrableOn
      (fun x => deriv (liPrimeMomentWeight j) x *
        (x * Real.exp (-c * Real.log x ^ ((1 : Real) / 10))))
      (Set.Ioi 1) := by
  have hp : (0 : Real) < (1 : Real) / 10 := by norm_num
  have hj := integrableOn_log_pow_div_mul_exp_neg_mul_log_rpow j hp hc
  have hjm := integrableOn_log_pow_div_mul_exp_neg_mul_log_rpow (j - 1) hp hc
  have hcomb : IntegrableOn
      (fun x : Real =>
        (j : Real) * (Real.log x ^ (j - 1) / x *
          Real.exp (-c * Real.log x ^ ((1 : Real) / 10))) -
        Real.log x ^ j / x *
          Real.exp (-c * Real.log x ^ ((1 : Real) / 10)))
      (Set.Ioi 1) := (hjm.const_mul (j : Real)).sub hj
  apply IntegrableOn.congr_fun hcomb _ measurableSet_Ioi
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  change _ = deriv (liPrimeMomentWeight j) x *
    (x * Real.exp (-c * Real.log x ^ ((1 : Real) / 10)))
  rw [deriv_liPrimeMomentWeight j hx0]
  simp only [liPrimeMomentWeightDeriv]
  field_simp [hx0]

/-- The weighted PNT remainder is absolutely integrable on `(1, ∞)`. -/
theorem integrableOn_weighted_liPrimeMomentPNTError (j : Nat) :
    IntegrableOn
      (fun x => deriv (liPrimeMomentWeight j) x * liPrimeMomentPNTError x)
      (Set.Ioi 1) := by
  obtain ⟨c, hc, hPNT⟩ := RiemannHypothesisProject.mediumPNT_remainder
  have hO :
      (fun x => deriv (liPrimeMomentWeight j) x * liPrimeMomentPNTError x) =O[atTop]
        (fun x => deriv (liPrimeMomentWeight j) x *
          (x * Real.exp (-c * Real.log x ^ ((1 : Real) / 10)))) := by
    simpa only [liPrimeMomentPNTError] using
      (isBigO_refl (deriv (liPrimeMomentWeight j)) atTop).mul hPNT
  have hmajorant := integrableOn_deriv_liPrimeMomentWeight_mul_pntMajorant j hc
  have hmajorantAt : IntegrableAtFilter
      (fun x => deriv (liPrimeMomentWeight j) x *
        (x * Real.exp (-c * Real.log x ^ ((1 : Real) / 10)))) atTop := by
    apply (integrableOn_Ici_iff_integrableAtFilter_atTop.mp
      (hmajorant.mono_set (show Set.Ici (2 : Real) ⊆ Set.Ioi 1 by
        intro x hx
        have hx' : (2 : Real) ≤ x := hx
        change (1 : Real) < x
        linarith))).1
  have hfull : IntegrableOn
      (fun x => deriv (liPrimeMomentWeight j) x * liPrimeMomentPNTError x)
      (Set.Ici 1) :=
    LocallyIntegrableOn.integrableOn_of_isBigO_atTop
      (locallyIntegrableOn_weighted_liPrimeMomentPNTError j) hO hmajorantAt
  exact hfull.mono_set Set.Ioi_subset_Ici_self

/-- A positive stretched exponential times any real power tends to zero. -/
theorem tendsto_rpow_mul_exp_neg_mul_rpow_atTop_nhds_zero_of_pos
    (s : Real) {p c : Real} (hp : 0 < p) (hc : 0 < c) :
    Tendsto (fun x : Real => x ^ s * Real.exp (-c * x ^ p))
      atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / p) c hc).comp
    (tendsto_rpow_atTop hp)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hx.le]
  congr 2
  field_simp [hp.ne']

theorem tendsto_log_pow_mul_exp_neg_mul_log_rpow_atTop_nhds_zero
    (j : Nat) {p c : Real} (hp : 0 < p) (hc : 0 < c) :
    Tendsto
      (fun x : Real => Real.log x ^ j *
        Real.exp (-c * Real.log x ^ p)) atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_rpow_atTop_nhds_zero_of_pos
    (j : Real) hp hc).comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
  simp only [Function.comp_apply, Real.rpow_natCast]

/-- The endpoint error in finite partial summation vanishes for every moment
index. -/
theorem tendsto_liPrimeMomentWeight_mul_pntError (j : Nat) :
    Tendsto
      (fun N : Nat => liPrimeMomentWeight j N * liPrimeMomentPNTError N)
      atTop (nhds 0) := by
  obtain ⟨c, hc, hPNT⟩ := RiemannHypothesisProject.mediumPNT_remainder
  have hO :
      (fun x : Real => liPrimeMomentWeight j x * liPrimeMomentPNTError x) =O[atTop]
        (fun x : Real => liPrimeMomentWeight j x *
          (x * Real.exp (-c * Real.log x ^ ((1 : Real) / 10)))) := by
    simpa only [liPrimeMomentPNTError] using
      (isBigO_refl (liPrimeMomentWeight j) atTop).mul hPNT
  have hmajorant : Tendsto
      (fun x : Real => liPrimeMomentWeight j x *
        (x * Real.exp (-c * Real.log x ^ ((1 : Real) / 10))))
      atTop (nhds 0) := by
    apply (tendsto_log_pow_mul_exp_neg_mul_log_rpow_atTop_nhds_zero j
      (by norm_num : (0 : Real) < (1 : Real) / 10) hc).congr'
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
    simp only [liPrimeMomentWeight]
    field_simp [hx0]
  exact (hO.trans_tendsto hmajorant).comp tendsto_natCast_atTop_atTop

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
