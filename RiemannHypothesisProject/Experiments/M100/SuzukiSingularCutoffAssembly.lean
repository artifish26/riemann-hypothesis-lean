import RiemannHypothesisProject.Experiments.M100.SuzukiSingularDifferenceCutoff

/-!
# M100-DF6D2 physical cutoff assembly

This module expands the finite reciprocal-kernel physical pairing into its
norm-difference and endpoint-row pieces.  It keeps all Fubini and integrability
inputs explicit before taking either cutoff limit.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set Filter
open scoped ComplexConjugate Interval Topology

def suzukiReciprocalCutoffXEnergyIntegrand
    (ε R : Real) (v : SchwartzLineTestFunction)
    (p : Real × Real) : Real :=
  (suzukiReciprocalCutoffKernel ε R (p.1 - p.2)).re * ‖v p.1‖ ^ 2

def suzukiReciprocalCutoffYEnergyIntegrand
    (ε R : Real) (v : SchwartzLineTestFunction)
    (p : Real × Real) : Real :=
  (suzukiReciprocalCutoffKernel ε R (p.1 - p.2)).re * ‖v p.2‖ ^ 2

def suzukiReciprocalCutoffDifferenceIntegrand
    (ε R : Real) (v : SchwartzLineTestFunction)
    (p : Real × Real) : Real :=
  (suzukiReciprocalCutoffKernel ε R (p.1 - p.2)).re *
    ‖v p.1 - v p.2‖ ^ 2

def suzukiReciprocalCutoffRealCrossIntegrand
    (ε R : Real) (v : SchwartzLineTestFunction)
    (p : Real × Real) : Real :=
  (suzukiReciprocalCutoffKernel ε R (p.1 - p.2) *
    v p.2 * conj (v p.1)).re

private theorem integrableOn_re_suzukiReciprocalCutoffKernel_mul_continuous
    {ε R a : Real} (hε : 0 < ε) {g : Real × Real → Real}
    (hg : Continuous g) :
    IntegrableOn
      (fun p : Real × Real =>
        (suzukiReciprocalCutoffKernel ε R (p.1 - p.2)).re * g p)
      (suzukiFiniteSquare a) := by
  have hgInt : IntegrableOn g (suzukiFiniteSquare a) :=
    hg.continuousOn.integrableOn_compact (isCompact_suzukiFiniteSquare a)
  apply hgInt.bdd_mul
  · exact (Complex.measurable_re.comp
      ((measurable_suzukiReciprocalCutoffKernel ε R).comp
        (by fun_prop : Measurable (fun p : Real × Real => p.1 - p.2))))
          |>.aestronglyMeasurable
  · filter_upwards with p
    exact (by
      simpa only [Real.norm_eq_abs] using
        (Complex.abs_re_le_norm
          (suzukiReciprocalCutoffKernel ε R (p.1 - p.2))).trans
            (norm_suzukiReciprocalCutoffKernel_le hε (p.1 - p.2)))

theorem integrableOn_suzukiReciprocalCutoffXEnergyIntegrand
    {ε R a : Real} (hε : 0 < ε) (v : SchwartzLineTestFunction) :
    IntegrableOn (suzukiReciprocalCutoffXEnergyIntegrand ε R v)
      (suzukiFiniteSquare a) := by
  exact integrableOn_re_suzukiReciprocalCutoffKernel_mul_continuous hε
    (by fun_prop)

theorem integrableOn_suzukiReciprocalCutoffYEnergyIntegrand
    {ε R a : Real} (hε : 0 < ε) (v : SchwartzLineTestFunction) :
    IntegrableOn (suzukiReciprocalCutoffYEnergyIntegrand ε R v)
      (suzukiFiniteSquare a) := by
  exact integrableOn_re_suzukiReciprocalCutoffKernel_mul_continuous hε
    (by fun_prop)

theorem integrableOn_suzukiReciprocalCutoffDifferenceIntegrand
    {ε R a : Real} (hε : 0 < ε) (v : SchwartzLineTestFunction) :
    IntegrableOn (suzukiReciprocalCutoffDifferenceIntegrand ε R v)
      (suzukiFiniteSquare a) := by
  exact integrableOn_re_suzukiReciprocalCutoffKernel_mul_continuous hε
    (by fun_prop)

private theorem integrableOn_suzukiReciprocalCutoffComplexCrossIntegrand
    {ε R a : Real} (hε : 0 < ε) (v : SchwartzLineTestFunction) :
    IntegrableOn
      (fun p : Real × Real =>
        suzukiReciprocalCutoffKernel ε R (p.1 - p.2) *
          v p.2 * conj (v p.1))
      (suzukiFiniteSquare a) := by
  have hbase : IntegrableOn
      (fun p : Real × Real => v p.2 * conj (v p.1))
      (suzukiFiniteSquare a) :=
    (by fun_prop : Continuous (fun p : Real × Real =>
      v p.2 * conj (v p.1))).continuousOn.integrableOn_compact
        (isCompact_suzukiFiniteSquare a)
  have hmul := hbase.bdd_mul
    (((measurable_suzukiReciprocalCutoffKernel ε R).comp
      (by fun_prop : Measurable (fun p : Real × Real => p.1 - p.2)))
        |>.aestronglyMeasurable)
    (by
      filter_upwards with p
      exact norm_suzukiReciprocalCutoffKernel_le hε (p.1 - p.2))
  change Integrable
    (fun p : Real × Real =>
      suzukiReciprocalCutoffKernel ε R (p.1 - p.2) *
        v p.2 * conj (v p.1))
    (volume.restrict (suzukiFiniteSquare a))
  simpa only [Function.comp_apply, mul_assoc] using hmul

theorem integrableOn_suzukiReciprocalCutoffRealCrossIntegrand
    {ε R a : Real} (hε : 0 < ε) (v : SchwartzLineTestFunction) :
    IntegrableOn (suzukiReciprocalCutoffRealCrossIntegrand ε R v)
      (suzukiFiniteSquare a) := by
  exact (integrableOn_suzukiReciprocalCutoffComplexCrossIntegrand hε v).re

/-- Pointwise polarization of the reciprocal-kernel norm difference. -/
theorem suzukiReciprocalCutoffDifferenceIntegrand_eq
    (ε R : Real) (v : SchwartzLineTestFunction) (p : Real × Real) :
    suzukiReciprocalCutoffDifferenceIntegrand ε R v p =
      suzukiReciprocalCutoffXEnergyIntegrand ε R v p +
        suzukiReciprocalCutoffYEnergyIntegrand ε R v p -
          2 * suzukiReciprocalCutoffRealCrossIntegrand ε R v p := by
  let K : Complex :=
    suzukiReciprocalCutoffKernel ε R (p.1 - p.2)
  let x : Complex := v p.1
  let y : Complex := v p.2
  have hKIm : K.im = 0 := by
    by_cases hmem : p.1 - p.2 ∈ suzukiReciprocalCutoffSet ε R
    · simp only [K, suzukiReciprocalCutoffKernel,
        Set.indicator_of_mem hmem, Complex.ofReal_im]
    · simp only [K, suzukiReciprocalCutoffKernel,
        Set.indicator_of_notMem hmem, Complex.zero_im]
  have hcrossSymm : (x * conj y).re = (y * conj x).re := by
    simp [Complex.mul_re]
    ring
  have hnorm :
      ‖x - y‖ ^ 2 =
        ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (y * conj x).re := by
    calc
      ‖x - y‖ ^ 2 = Complex.normSq (x - y) :=
        (Complex.normSq_eq_norm_sq _).symm
      _ = Complex.normSq x + Complex.normSq y -
          2 * (x * conj y).re := Complex.normSq_sub x y
      _ = Complex.normSq x + Complex.normSq y -
          2 * (y * conj x).re := by rw [hcrossSymm]
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 -
          2 * (y * conj x).re := by
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hcross :
      (K * y * conj x).re = K.re * (y * conj x).re := by
    rw [show K * y * conj x = K * (y * conj x) by ring,
      Complex.mul_re, hKIm]
    ring
  unfold suzukiReciprocalCutoffDifferenceIntegrand
    suzukiReciprocalCutoffXEnergyIntegrand
    suzukiReciprocalCutoffYEnergyIntegrand
    suzukiReciprocalCutoffRealCrossIntegrand
  change K.re * ‖x - y‖ ^ 2 =
    K.re * ‖x‖ ^ 2 + K.re * ‖y‖ ^ 2 - 2 * (K * y * conj x).re
  rw [hnorm, hcross]
  ring

/-- Fubini identifies the `x`-energy square term with the reciprocal row mass. -/
theorem integral_suzukiReciprocalCutoffXEnergyIntegrand_eq_rowMass
    {ε R a : Real} (hε : 0 < ε) (v : SchwartzLineTestFunction) :
    (∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffXEnergyIntegrand ε R v p) =
      ∫ x in Icc (-a) a,
        suzukiReciprocalCutoffRowMass ε R a x * ‖v x‖ ^ 2 := by
  have hX := integrableOn_suzukiReciprocalCutoffXEnergyIntegrand
    (R := R) (a := a) hε v
  rw [suzukiFiniteSquare, Measure.volume_eq_prod] at hX ⊢
  rw [MeasureTheory.setIntegral_prod
    (suzukiReciprocalCutoffXEnergyIntegrand ε R v) hX]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _hx
  unfold suzukiReciprocalCutoffXEnergyIntegrand
    suzukiReciprocalCutoffRowMass
  change
    (∫ y in Icc (-a) a,
      (suzukiReciprocalCutoffKernel ε R (x - y)).re * ‖v x‖ ^ 2) =
    (∫ y in Icc (-a) a,
      (suzukiReciprocalCutoffKernel ε R (x - y)).re) * ‖v x‖ ^ 2
  rw [← integral_mul_const]

/-- Evenness of the reciprocal kernel makes the two diagonal square-energy
terms equal. -/
theorem integral_suzukiReciprocalCutoffYEnergyIntegrand_eq_x
    (ε R a : Real) (v : SchwartzLineTestFunction) :
    (∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffYEnergyIntegrand ε R v p) =
      ∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffXEnergyIntegrand ε R v p := by
  rw [suzukiFiniteSquare, Measure.volume_eq_prod]
  calc
    (∫ p in Icc (-a) a ×ˢ Icc (-a) a,
        suzukiReciprocalCutoffYEnergyIntegrand ε R v p
          ∂volume.prod volume) =
        ∫ p in Icc (-a) a ×ˢ Icc (-a) a,
          suzukiReciprocalCutoffXEnergyIntegrand ε R v p.swap
            ∂volume.prod volume := by
      apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      intro p _hp
      rcases p with ⟨x, y⟩
      unfold suzukiReciprocalCutoffXEnergyIntegrand
        suzukiReciprocalCutoffYEnergyIntegrand
      simp only [Prod.swap_prod_mk]
      rw [show y - x = -(x - y) by ring,
        suzukiReciprocalCutoffKernel_neg]
    _ = ∫ p in Icc (-a) a ×ˢ Icc (-a) a,
          suzukiReciprocalCutoffXEnergyIntegrand ε R v p
            ∂volume.prod volume :=
      MeasureTheory.setIntegral_prod_swap (Icc (-a) a) (Icc (-a) a)
        (suzukiReciprocalCutoffXEnergyIntegrand ε R v)

/-- The real part of the finite complex square pairing is the integral of the
named real cross integrand. -/
theorem suzukiReciprocalCutoffSquarePairing_re_eq_realCross
    {ε R a : Real} (hε : 0 < ε) (v : SchwartzLineTestFunction) :
    (suzukiReciprocalCutoffSquarePairing ε R a v).re =
      ∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffRealCrossIntegrand ε R v p := by
  unfold suzukiReciprocalCutoffSquarePairing
    suzukiReciprocalCutoffRealCrossIntegrand
  exact (integral_re
    (integrableOn_suzukiReciprocalCutoffComplexCrossIntegrand hε v)).symm

/-- Integrated polarization of the cutoff norm difference. -/
theorem integral_suzukiReciprocalCutoffDifferenceIntegrand_eq
    {ε R a : Real} (hε : 0 < ε) (v : SchwartzLineTestFunction) :
    (∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffDifferenceIntegrand ε R v p) =
      2 * (∫ x in Icc (-a) a,
        suzukiReciprocalCutoffRowMass ε R a x * ‖v x‖ ^ 2) -
      2 * (suzukiReciprocalCutoffSquarePairing ε R a v).re := by
  have hX := integrableOn_suzukiReciprocalCutoffXEnergyIntegrand
    (R := R) (a := a) hε v
  have hY := integrableOn_suzukiReciprocalCutoffYEnergyIntegrand
    (R := R) (a := a) hε v
  have hC := integrableOn_suzukiReciprocalCutoffRealCrossIntegrand
    (R := R) (a := a) hε v
  have hsub := integral_sub (hX.add hY) (hC.const_mul 2)
  change
    (∫ p in suzukiFiniteSquare a,
      (suzukiReciprocalCutoffXEnergyIntegrand ε R v p +
        suzukiReciprocalCutoffYEnergyIntegrand ε R v p) -
          2 * suzukiReciprocalCutoffRealCrossIntegrand ε R v p) =
      (∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffXEnergyIntegrand ε R v p +
          suzukiReciprocalCutoffYEnergyIntegrand ε R v p) -
      (∫ p in suzukiFiniteSquare a,
        2 * suzukiReciprocalCutoffRealCrossIntegrand ε R v p) at hsub
  have hadd := integral_add hX hY
  change
    (∫ p in suzukiFiniteSquare a,
      suzukiReciprocalCutoffXEnergyIntegrand ε R v p +
        suzukiReciprocalCutoffYEnergyIntegrand ε R v p) =
      (∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffXEnergyIntegrand ε R v p) +
      (∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffYEnergyIntegrand ε R v p) at hadd
  have hmul :
      (∫ p in suzukiFiniteSquare a,
        2 * suzukiReciprocalCutoffRealCrossIntegrand ε R v p) =
      2 * (∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffRealCrossIntegrand ε R v p) := by
    rw [integral_const_mul]
  calc
    (∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffDifferenceIntegrand ε R v p) =
        ∫ p in suzukiFiniteSquare a,
          (suzukiReciprocalCutoffXEnergyIntegrand ε R v p +
            suzukiReciprocalCutoffYEnergyIntegrand ε R v p -
              2 * suzukiReciprocalCutoffRealCrossIntegrand ε R v p) := by
      apply integral_congr_ae
      filter_upwards with p
      exact suzukiReciprocalCutoffDifferenceIntegrand_eq ε R v p
    _ = (∫ p in suzukiFiniteSquare a,
          suzukiReciprocalCutoffXEnergyIntegrand ε R v p) +
        (∫ p in suzukiFiniteSquare a,
          suzukiReciprocalCutoffYEnergyIntegrand ε R v p) -
        2 * (∫ p in suzukiFiniteSquare a,
          suzukiReciprocalCutoffRealCrossIntegrand ε R v p) := by
      rw [hsub, hadd, hmul]
    _ = 2 * (∫ x in Icc (-a) a,
          suzukiReciprocalCutoffRowMass ε R a x * ‖v x‖ ^ 2) -
        2 * (suzukiReciprocalCutoffSquarePairing ε R a v).re := by
      rw [integral_suzukiReciprocalCutoffYEnergyIntegrand_eq_x,
        integral_suzukiReciprocalCutoffXEnergyIntegrand_eq_rowMass hε v,
        suzukiReciprocalCutoffSquarePairing_re_eq_realCross hε v]
      ring

/-- On the interior of the finite interval, adding both renormalizing
logarithms converts the reciprocal row mass into the two clamped endpoint
logarithms. -/
theorem suzukiReciprocalCutoffRowMass_add_two_log
    {ε R a x : Real} (hε : 0 < ε) (ha : 0 ≤ a)
    (hx : x ∈ Ioo (-a) a) (hR : 2 * a ≤ R) :
    suzukiReciprocalCutoffRowMass ε R a x + 2 * Real.log ε =
      suzukiClampedLog ε (a - x) + suzukiClampedLog ε (a + x) := by
  have hxIcc : x ∈ Icc (-a) a := ⟨hx.1.le, hx.2.le⟩
  have hright : 0 < a - x := sub_pos.mpr hx.2
  have hleft : 0 < a + x := by linarith [hx.1]
  calc
    suzukiReciprocalCutoffRowMass ε R a x + 2 * Real.log ε =
        (suzukiOneSidedReciprocalMass ε (a - x) + Real.log ε) +
          (suzukiOneSidedReciprocalMass ε (a + x) + Real.log ε) := by
      rw [suzukiReciprocalCutoffRowMass_eq hε ha hxIcc hR]
      ring
    _ = suzukiClampedLog ε (a - x) +
        suzukiClampedLog ε (a + x) := by
      rw [suzukiOneSidedReciprocalMass_add_log hε hright,
        suzukiOneSidedReciprocalMass_add_log hε hleft]

/-- A smooth-core function has the same norm-square integral globally as on
its closed support interval. -/
theorem integral_normSq_suzukiSmoothCore_eq_Icc
    {a : Real} (v : SuzukiSmoothCore a) :
    (∫ x : Real, ‖v.1 x‖ ^ 2) =
      ∫ x in Icc (-a) a, ‖v.1 x‖ ^ 2 := by
  have hsupport : Function.support v.1 ⊆ Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hvx : v.1 x = 0 := by
    by_contra hne
    exact hx (hsupport hne)
  simp [hvx]

/-- Once the outer cutoff contains the finite square, its difference integral
is exactly the named inner-cutoff difference integral. -/
theorem integral_suzukiReciprocalCutoffDifferenceIntegrand_eq_cutoff
    {ε R a : Real} (hR : 2 * a ≤ R) (v : SchwartzLineTestFunction) :
    (∫ p in suzukiFiniteSquare a,
        suzukiReciprocalCutoffDifferenceIntegrand ε R v p) =
      ∫ p in suzukiFiniteSquare a,
        suzukiCutoffSingularDifferenceIntegrand ε v p := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    (isCompact_suzukiFiniteSquare a).measurableSet] with p hp
  exact re_suzukiReciprocalCutoffKernel_mul_normSq_eq_cutoff hR v hp

/-- The row energy plus the global logarithmic renormalization is exactly the
clamped boundary integral. -/
theorem suzukiReciprocalCutoffRowEnergy_add_log_eq_boundary
    {ε R a : Real} (hε : 0 < ε) (hεOne : ε ≤ 1) (ha : 0 < a)
    (hR : 2 * a ≤ R) (v : SuzukiSmoothCore a) :
    (∫ x in Icc (-a) a,
        suzukiReciprocalCutoffRowMass ε R a x * ‖v.1 x‖ ^ 2) +
      2 * Real.log ε * (∫ x : Real, ‖v.1 x‖ ^ 2) =
        ∫ x in Icc (-a) a,
          suzukiBoundaryCutoffIntegrand ε a v.1 x := by
  let μ : Measure Real := volume.restrict (Icc (-a) a)
  have hneLeft : ∀ᵐ x ∂μ, x ≠ -a :=
    (ae_mono Measure.restrict_le_self) (volume.ae_ne (-a))
  have hneRight : ∀ᵐ x ∂μ, x ≠ a :=
    (ae_mono Measure.restrict_le_self) (volume.ae_ne a)
  have hpoint : ∀ᵐ x ∂μ,
      suzukiReciprocalCutoffRowMass ε R a x * ‖v.1 x‖ ^ 2 +
          2 * Real.log ε * ‖v.1 x‖ ^ 2 =
        suzukiBoundaryCutoffIntegrand ε a v.1 x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      hneLeft, hneRight] with x hx hxLeft hxRight
    have hxIoo : x ∈ Ioo (-a) a :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxLeft),
        lt_of_le_of_ne hx.2 hxRight⟩
    have hrow := suzukiReciprocalCutoffRowMass_add_two_log
      hε ha.le hxIoo hR
    unfold suzukiBoundaryCutoffIntegrand
    rw [← hrow]
    ring
  have hboundary := integrableOn_suzukiBoundaryCutoffIntegrand
    hε hεOne ha.le v.1
  have hconstant : IntegrableOn
      (fun x : Real => 2 * Real.log ε * ‖v.1 x‖ ^ 2)
      (Icc (-a) a) :=
    (by fun_prop : Continuous (fun x : Real =>
      2 * Real.log ε * ‖v.1 x‖ ^ 2)).continuousOn.integrableOn_compact
        isCompact_Icc
  have hrow : IntegrableOn
      (fun x : Real =>
        suzukiReciprocalCutoffRowMass ε R a x * ‖v.1 x‖ ^ 2)
      (Icc (-a) a) := by
    apply (hboundary.sub hconstant).congr
    filter_upwards [hpoint] with x hx
    change
      suzukiBoundaryCutoffIntegrand ε a v.1 x -
          2 * Real.log ε * ‖v.1 x‖ ^ 2 =
        suzukiReciprocalCutoffRowMass ε R a x * ‖v.1 x‖ ^ 2
    linarith
  calc
    (∫ x in Icc (-a) a,
        suzukiReciprocalCutoffRowMass ε R a x * ‖v.1 x‖ ^ 2) +
        2 * Real.log ε * (∫ x : Real, ‖v.1 x‖ ^ 2) =
      (∫ x in Icc (-a) a,
        suzukiReciprocalCutoffRowMass ε R a x * ‖v.1 x‖ ^ 2) +
        2 * Real.log ε * (∫ x in Icc (-a) a, ‖v.1 x‖ ^ 2) := by
      rw [integral_normSq_suzukiSmoothCore_eq_Icc v]
    _ = (∫ x in Icc (-a) a,
          suzukiReciprocalCutoffRowMass ε R a x * ‖v.1 x‖ ^ 2) +
        (∫ x in Icc (-a) a,
          2 * Real.log ε * ‖v.1 x‖ ^ 2) := by
      rw [integral_const_mul]
    _ = ∫ x in Icc (-a) a,
        (suzukiReciprocalCutoffRowMass ε R a x * ‖v.1 x‖ ^ 2 +
          2 * Real.log ε * ‖v.1 x‖ ^ 2) :=
      (integral_add hrow hconstant).symm
    _ = ∫ x in Icc (-a) a,
        suzukiBoundaryCutoffIntegrand ε a v.1 x :=
      integral_congr_ae hpoint

/-- Exact finite-cutoff physical decomposition. -/
theorem suzukiRenormalizedCutoffPhysicalPairing_eq_difference_sub_boundary
    {ε R a : Real} (hε : 0 < ε) (hεOne : ε ≤ 1) (ha : 0 < a)
    (hR : 2 * a ≤ R) (v : SuzukiSmoothCore a) :
    suzukiRenormalizedCutoffPhysicalPairing ε R v.1 =
      (1 / 2 : Real) *
          (∫ p in suzukiFiniteSquare a,
            suzukiCutoffSingularDifferenceIntegrand ε v.1 p) -
        ∫ x in Icc (-a) a,
          suzukiBoundaryCutoffIntegrand ε a v.1 x := by
  have hphysical :=
    suzukiReciprocalCutoffAutocorrelationPairing_eq_square
      (R := R) hε v
  have hdifference :=
    integral_suzukiReciprocalCutoffDifferenceIntegrand_eq
      (R := R) (a := a) hε v.1
  have hcutoff :=
    integral_suzukiReciprocalCutoffDifferenceIntegrand_eq_cutoff
      (ε := ε) hR v.1
  have hboundary := suzukiReciprocalCutoffRowEnergy_add_log_eq_boundary
    hε hεOne ha hR v
  unfold suzukiRenormalizedCutoffPhysicalPairing
  rw [hphysical]
  rw [← hcutoff]
  linarith

end

end M100
end Experiments
end RiemannHypothesisProject
