import RiemannHypothesisProject.Experiments.M100.SuzukiSingularFourierCutoff
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# M100-DF6D2 cosine-integral asymptotic

This module develops the special-function input isolated by the finite
reciprocal-kernel calculation.  The convergence is split into a regular
near-zero integral and an oscillatory tail.  Their sum is the classical
cosine-integral constant; identifying that constant with the negative
Euler--Mascheroni constant is kept as a separately named source theorem.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set Filter intervalIntegral
open scoped Interval Topology

/-- The removable near-zero part of the cosine integral.  Lean's totalized
division supplies the value zero at the origin. -/
def suzukiCosineRegularPart (t : Real) : Real :=
  (Real.cos t - 1) / t

/-- Quadratic cancellation of `cos t - 1` removes the apparent singularity. -/
theorem abs_suzukiCosineRegularPart_le
    (t : Real) :
    abs (suzukiCosineRegularPart t) ≤ |t| / 2 := by
  by_cases ht : t = 0
  · subst t
    simp [suzukiCosineRegularPart]
  · have htAbs : 0 < |t| := abs_pos.mpr ht
    have hcosUpper : Real.cos t ≤ 1 := Real.cos_le_one t
    have hcosLower : 1 - t ^ 2 / 2 ≤ Real.cos t :=
      Real.one_sub_sq_div_two_le_cos
    have hnum : abs (Real.cos t - 1) = 1 - Real.cos t := by
      rw [abs_of_nonpos (sub_nonpos.mpr hcosUpper)]
      ring
    rw [suzukiCosineRegularPart, abs_div, hnum]
    apply (div_le_iff₀ htAbs).2
    have htSq : t ^ 2 = |t| ^ 2 := by
      rw [sq_abs]
    rw [htSq] at hcosLower
    nlinarith

/-- The regular part is integrable on the unit interval, including zero. -/
theorem integrableOn_suzukiCosineRegularPart :
    IntegrableOn suzukiCosineRegularPart (Icc (-1) 1) := by
  apply Measure.integrableOn_of_bounded
    isCompact_Icc.measure_ne_top
    (by
      apply Measurable.aestronglyMeasurable
      unfold suzukiCosineRegularPart
      fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have htAbs : |t| ≤ 1 := (abs_le).2 ht
  calc
    ‖suzukiCosineRegularPart t‖ =
        abs (suzukiCosineRegularPart t) := Real.norm_eq_abs _
    _ ≤ |t| / 2 := abs_suzukiCosineRegularPart_le t
    _ ≤ 1 / 2 := by linarith

/-- The removable definition of the regular part is continuous even at the
origin. -/
theorem continuous_suzukiCosineRegularPart :
    Continuous suzukiCosineRegularPart := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · subst t
    have hmajor :
        Tendsto (fun s : Real => |s| / 2) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun s : Real => |s| / (2 : Real)) :=
        continuous_abs.div_const (2 : Real)
      simpa using hcont.tendsto 0
    have habs :
        Tendsto (fun s : Real => abs (suzukiCosineRegularPart s))
          (𝓝 0) (𝓝 0) := by
      apply squeeze_zero
      · intro s
        exact abs_nonneg _
      · exact abs_suzukiCosineRegularPart_le
      · exact hmajor
    change Tendsto suzukiCosineRegularPart (𝓝 0)
      (𝓝 (suzukiCosineRegularPart 0))
    have hzero : suzukiCosineRegularPart 0 = 0 := by
      simp [suzukiCosineRegularPart]
    rw [hzero]
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  · unfold suzukiCosineRegularPart
    exact (Real.continuous_cos.continuousAt.sub continuousAt_const).div
      continuousAt_id ht

/-- Integration by parts for the oscillatory tail. -/
theorem integral_cos_div_eq_boundary_add
    {R S : Real} (hR : 0 < R) (hRS : R ≤ S) :
    (∫ t in R..S, Real.cos t / t) =
      Real.sin S / S - Real.sin R / R +
        ∫ t in R..S, Real.sin t / t ^ 2 := by
  have hpos {t : Real} (ht : t ∈ [[R, S]]) : 0 < t := by
    rw [uIcc_of_le hRS] at ht
    exact hR.trans_le ht.1
  have hu : ∀ t ∈ [[R, S]],
      HasDerivAt (fun x : Real => x⁻¹) (-(1 / t ^ 2)) t := by
    intro t ht
    have ht0 : t ≠ 0 := (hpos ht).ne'
    have hi := (hasDerivAt_id t).inv ht0
    have hfun : (id : Real → Real)⁻¹ = (fun x : Real => x⁻¹) := by
      funext x
      rfl
    rw [hfun] at hi
    simp only [id_eq] at hi
    exact hi.congr_deriv (by ring)
  have hv : ∀ t ∈ [[R, S]],
      HasDerivAt Real.sin (Real.cos t) t := by
    intro t ht
    exact Real.hasDerivAt_sin t
  have huInt : IntervalIntegrable (fun t : Real => -(1 / t ^ 2)) volume R S := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact ((continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (hpos ht).ne')).neg).continuousWithinAt
  have hvInt : IntervalIntegrable Real.cos volume R S :=
    Real.continuous_cos.intervalIntegrable R S
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv huInt hvInt
  have hleft :
      (∫ t in R..S, Real.cos t / t) =
        ∫ t in R..S, t⁻¹ * Real.cos t := by
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hneg :
      (∫ t in R..S, -(1 / t ^ 2) * Real.sin t) =
        -(∫ t in R..S, Real.sin t / t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hleft, hparts, hneg]
  ring

/-- Exact integral of the positive inverse-square majorant. -/
theorem integral_one_div_sq
    {R S : Real} (hR : 0 < R) (hRS : R ≤ S) :
    (∫ t in R..S, 1 / t ^ 2) = 1 / R - 1 / S := by
  have hpos {t : Real} (ht : t ∈ [[R, S]]) : 0 < t := by
    rw [uIcc_of_le hRS] at ht
    exact hR.trans_le ht.1
  have hderiv : ∀ t ∈ [[R, S]],
      HasDerivAt (fun x : Real => -x⁻¹) (1 / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := (hpos ht).ne'
    have hi' : HasDerivAt (fun x : Real => x⁻¹) (-(1 / t ^ 2)) t := by
      have hi := (hasDerivAt_id t).inv ht0
      have hfun : (id : Real → Real)⁻¹ = (fun x : Real => x⁻¹) := by
        funext x
        rfl
      rw [hfun] at hi
      simp only [id_eq] at hi
      exact hi.congr_deriv (by ring)
    have hneg := hi'.neg
    have hfun : -(fun x : Real => x⁻¹) = (fun x : Real => -x⁻¹) := by
      funext x
      rfl
    rw [hfun] at hneg
    simpa only [neg_neg] using hneg
  have hint : IntervalIntegrable (fun t : Real => 1 / t ^ 2)
      volume R S := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (hpos ht).ne')).continuousWithinAt
  simpa [one_div, sub_eq_add_neg, add_comm] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Dirichlet tail bound.  The constant `3` is deliberately coarse but is
uniform in the upper endpoint. -/
theorem abs_integral_cos_div_le
    {R S : Real} (hR : 1 ≤ R) (hRS : R ≤ S) :
    abs (∫ t in R..S, Real.cos t / t) ≤ 3 / R := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hSpos : 0 < S := hRpos.trans_le hRS
  have hsinInt : IntervalIntegrable (fun t : Real => Real.sin t / t ^ 2)
      volume R S := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hRS] at ht
    have htpos : 0 < t := hRpos.trans_le ht.1
    exact (Real.continuous_sin.continuousAt.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 htpos.ne')).continuousWithinAt
  have hinvInt : IntervalIntegrable (fun t : Real => 1 / t ^ 2)
      volume R S := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hRS] at ht
    have htpos : 0 < t := hRpos.trans_le ht.1
    exact (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 htpos.ne')).continuousWithinAt
  have htailAbs :
      abs (∫ t in R..S, Real.sin t / t ^ 2) ≤
        ∫ t in R..S, 1 / t ^ 2 := by
    calc
      abs (∫ t in R..S, Real.sin t / t ^ 2) ≤
          ∫ t in R..S, abs (Real.sin t / t ^ 2) :=
        intervalIntegral.abs_integral_le_integral_abs hRS
      _ ≤ ∫ t in R..S, 1 / t ^ 2 := by
        apply intervalIntegral.integral_mono_on hRS
          hsinInt.abs hinvInt
        intro t ht
        have htpos : 0 < t := hRpos.trans_le ht.1
        rw [abs_div, abs_of_pos (sq_pos_of_pos htpos)]
        exact div_le_div_of_nonneg_right
          (Real.abs_sin_le_one t) (sq_nonneg t)
  have htail :
      abs (∫ t in R..S, Real.sin t / t ^ 2) ≤ 1 / R := by
    calc
      abs (∫ t in R..S, Real.sin t / t ^ 2) ≤
          ∫ t in R..S, 1 / t ^ 2 := htailAbs
      _ = 1 / R - 1 / S := integral_one_div_sq hRpos hRS
      _ ≤ 1 / R := by
        have : 0 < 1 / S := one_div_pos.mpr hSpos
        linarith
  rw [integral_cos_div_eq_boundary_add hRpos hRS]
  calc
    abs (Real.sin S / S - Real.sin R / R +
        ∫ t in R..S, Real.sin t / t ^ 2) ≤
        abs (Real.sin S / S) + abs (Real.sin R / R) +
          abs (∫ t in R..S, Real.sin t / t ^ 2) := by
      calc
        abs (Real.sin S / S - Real.sin R / R +
            ∫ t in R..S, Real.sin t / t ^ 2) ≤
            abs (Real.sin S / S - Real.sin R / R) +
              abs (∫ t in R..S, Real.sin t / t ^ 2) :=
          abs_add_le _ _
        _ ≤ (abs (Real.sin S / S) + abs (Real.sin R / R)) +
              abs (∫ t in R..S, Real.sin t / t ^ 2) :=
          by gcongr; exact abs_sub _ _
    _ ≤ 1 / R + 1 / R + 1 / R := by
      have hfirst : abs (Real.sin S / S) ≤ 1 / R := by
        rw [abs_div, abs_of_pos hSpos]
        exact (div_le_div_of_nonneg_right (Real.abs_sin_le_one S)
          hSpos.le).trans (one_div_le_one_div_of_le hRpos hRS)
      have hsecond : abs (Real.sin R / R) ≤ 1 / R := by
        rw [abs_div, abs_of_pos hRpos]
        exact div_le_div_of_nonneg_right (Real.abs_sin_le_one R) hRpos.le
      gcongr
    _ = 3 / R := by ring

/-- The cosine quotient is integrable on any interval whose endpoints are at
least one. -/
theorem intervalIntegrable_cos_div_of_one_le
    {a b : Real} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable (fun t : Real => Real.cos t / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have htOne : 1 ≤ t := (le_min ha hb).trans ht.1
  have ht0 : t ≠ 0 := (zero_lt_one.trans_le htOne).ne'
  exact (Real.continuous_cos.continuousAt.div continuousAt_id ht0).continuousWithinAt

/-- Natural upper cutoffs used to construct the improper cosine tail. -/
def suzukiCosineTailPartial (n : Nat) : Real :=
  ∫ t in (1 : Real)..(n + 1 : Nat), Real.cos t / t

theorem suzukiCosineTailPartial_sub
    (n m : Nat) :
    suzukiCosineTailPartial m - suzukiCosineTailPartial n =
      ∫ t in (n + 1 : Nat)..(m + 1 : Nat), Real.cos t / t := by
  have hOneN : (1 : Real) ≤ (n + 1 : Nat) := by norm_num
  have hOneM : (1 : Real) ≤ (m + 1 : Nat) := by norm_num
  have hleft := intervalIntegrable_cos_div_of_one_le
    (le_refl (1 : Real)) hOneN
  have hright := intervalIntegrable_cos_div_of_one_le hOneN hOneM
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  unfold suzukiCosineTailPartial
  linarith

/-- The natural-cutoff cosine tail is Cauchy by the uniform Dirichlet bound. -/
theorem cauchySeq_suzukiCosineTailPartial :
    CauchySeq suzukiCosineTailPartial := by
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / δ)
  have hNδ : 3 / ((N : Real) + 1) < δ := by
    have hmul : 3 < (N : Real) * δ :=
      (div_lt_iff₀ hδ).1 hN
    have hden : 0 < (N : Real) + 1 := by positivity
    apply (div_lt_iff₀ hden).2
    nlinarith
  refine ⟨N, ?_⟩
  intro m hm n hn
  by_cases hnm : n ≤ m
  · rw [Real.dist_eq, suzukiCosineTailPartial_sub]
    have htail := abs_integral_cos_div_le
      (R := (n + 1 : Nat)) (S := (m + 1 : Nat))
      (by norm_num) (by exact_mod_cast Nat.add_le_add_right hnm 1)
    have htail' :
        abs (∫ t in (n + 1 : Nat)..(m + 1 : Nat), Real.cos t / t) ≤
          3 / ((n : Real) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using htail
    have hmono :
        3 / ((n : Real) + 1) ≤ 3 / ((N : Real) + 1) := by
      have hNden : 0 < (N : Real) + 1 := by positivity
      have hnDen : (N : Real) + 1 ≤ (n : Real) + 1 := by
        exact_mod_cast Nat.add_le_add_right hn 1
      exact div_le_div_of_nonneg_left (by norm_num) hNden hnDen
    exact htail'.trans_lt (hmono.trans_lt hNδ)
  · have hmn : m ≤ n := Nat.le_of_not_ge hnm
    rw [dist_comm, Real.dist_eq, suzukiCosineTailPartial_sub]
    have htail := abs_integral_cos_div_le
      (R := (m + 1 : Nat)) (S := (n + 1 : Nat))
      (by norm_num) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    have htail' :
        abs (∫ t in (m + 1 : Nat)..(n + 1 : Nat), Real.cos t / t) ≤
          3 / ((m : Real) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using htail
    have hmono :
        3 / ((m : Real) + 1) ≤ 3 / ((N : Real) + 1) := by
      have hNden : 0 < (N : Real) + 1 := by positivity
      have hmDen : (N : Real) + 1 ≤ (m : Real) + 1 := by
        exact_mod_cast Nat.add_le_add_right hm 1
      exact div_le_div_of_nonneg_left (by norm_num) hNden hmDen
    exact htail'.trans_lt (hmono.trans_lt hNδ)

/-- The classical improper tail `∫₁^∞ cos t / t dt`, constructed without
pretending that it is absolutely Bochner-integrable. -/
def suzukiCosineTailConstant : Real :=
  limUnder atTop suzukiCosineTailPartial

theorem tendsto_suzukiCosineTailPartial :
    Tendsto suzukiCosineTailPartial atTop
      (𝓝 suzukiCosineTailConstant) := by
  exact cauchySeq_suzukiCosineTailPartial.tendsto_limUnder

/-- The same oscillatory tail with an arbitrary real upper endpoint. -/
def suzukiCosineTailPartialReal (R : Real) : Real :=
  ∫ t in (1 : Real)..R, Real.cos t / t

/-- The natural-cutoff construction controls every real upper cutoff. -/
theorem tendsto_suzukiCosineTailPartialReal :
    Tendsto suzukiCosineTailPartialReal atTop
      (𝓝 suzukiCosineTailConstant) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ :=
    (Metric.tendsto_atTop.1 tendsto_suzukiCosineTailPartial)
      (δ / 2) (half_pos hδ)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (6 / δ)
  let N := max N₀ N₁
  have hclose :
      dist (suzukiCosineTailPartial N) suzukiCosineTailConstant <
        δ / 2 :=
    hN₀ N (le_max_left _ _)
  have hsmall : 3 / ((N : Real) + 1) < δ / 2 := by
    have hNlarge : 6 / δ < (N : Real) :=
      hN₁.trans_le (by exact_mod_cast le_max_right N₀ N₁)
    have hmul : 6 < (N : Real) * δ :=
      (div_lt_iff₀ hδ).1 hNlarge
    have hden : 0 < (N : Real) + 1 := by positivity
    apply (div_lt_iff₀ hden).2
    nlinarith
  refine ⟨(N : Real) + 1, ?_⟩
  intro R hR
  have hOneN : (1 : Real) ≤ (N : Real) + 1 := by norm_num
  have hleft := intervalIntegrable_cos_div_of_one_le
    (le_refl (1 : Real)) hOneN
  have hright := intervalIntegrable_cos_div_of_one_le hOneN
    (hOneN.trans hR)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hsplit :
      suzukiCosineTailPartialReal R - suzukiCosineTailPartial N =
        ∫ t in ((N : Real) + 1)..R, Real.cos t / t := by
    unfold suzukiCosineTailPartialReal suzukiCosineTailPartial
    rw [← hadd]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have htail := abs_integral_cos_div_le hOneN hR
  rw [Real.dist_eq]
  calc
    abs (suzukiCosineTailPartialReal R - suzukiCosineTailConstant) ≤
        abs (suzukiCosineTailPartialReal R - suzukiCosineTailPartial N) +
          abs (suzukiCosineTailPartial N - suzukiCosineTailConstant) := by
      rw [show suzukiCosineTailPartialReal R - suzukiCosineTailConstant =
          (suzukiCosineTailPartialReal R - suzukiCosineTailPartial N) +
            (suzukiCosineTailPartial N - suzukiCosineTailConstant) by ring]
      exact abs_add_le _ _
    _ ≤ 3 / ((N : Real) + 1) +
          dist (suzukiCosineTailPartial N) suzukiCosineTailConstant := by
      rw [hsplit, Real.dist_eq]
      gcongr
    _ < δ := by linarith

/-- The absolutely integrable regular contribution on `[0,1]`. -/
def suzukiCosineRegularConstant : Real :=
  ∫ t in (0 : Real)..1, suzukiCosineRegularPart t

/-- The regular contribution with a positive lower cutoff. -/
def suzukiCosineRegularPartial (s : Real) : Real :=
  ∫ t in s..1, suzukiCosineRegularPart t

/-- A regular-part segment contained in `[0,1]` has a uniform elementary
bound. -/
theorem abs_integral_suzukiCosineRegularPart_le_half
    {s T : Real} (hs : 0 ≤ s) (hsT : s ≤ T) (hT : T ≤ 1) :
    abs (∫ t in s..T, suzukiCosineRegularPart t) ≤ 1 / 2 := by
  have hnorm :
      ‖∫ t in s..T, suzukiCosineRegularPart t‖ ≤
        (1 / 2 : Real) * |T - s| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have htIcc : t ∈ Icc s T := by
      simpa only [uIcc_of_le hsT] using uIoc_subset_uIcc ht
    calc
      ‖suzukiCosineRegularPart t‖ =
          abs (suzukiCosineRegularPart t) := Real.norm_eq_abs _
      _ ≤ |t| / 2 := abs_suzukiCosineRegularPart_le t
      _ ≤ 1 / 2 := by
        rw [abs_of_nonneg (hs.trans htIcc.1)]
        nlinarith [htIcc.2]
  rw [Real.norm_eq_abs] at hnorm
  calc
    abs (∫ t in s..T, suzukiCosineRegularPart t) ≤
        (1 / 2 : Real) * |T - s| := hnorm
    _ ≤ 1 / 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsT)]
      nlinarith

/-- The real-cutoff tail is uniformly bounded after one. -/
theorem abs_suzukiCosineTailPartialReal_le_three
    {R : Real} (hR : 1 ≤ R) :
    abs (suzukiCosineTailPartialReal R) ≤ 3 := by
  unfold suzukiCosineTailPartialReal
  simpa using abs_integral_cos_div_le (R := (1 : Real)) (S := R)
    (le_refl (1 : Real)) hR

theorem suzukiCosineRegularPartial_eq (s : Real) :
    suzukiCosineRegularPartial s =
      suzukiCosineRegularConstant -
        ∫ t in (0 : Real)..s, suzukiCosineRegularPart t := by
  have hleft := continuous_suzukiCosineRegularPart.intervalIntegrable
    (μ := volume) 0 s
  have hright := continuous_suzukiCosineRegularPart.intervalIntegrable
    (μ := volume) s 1
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  unfold suzukiCosineRegularPartial suzukiCosineRegularConstant
  linarith

/-- The regular cutoff converges to its complete contribution as the lower
endpoint tends to zero from the right. -/
theorem tendsto_suzukiCosineRegularPartial :
    Tendsto suzukiCosineRegularPartial (𝓝[>] (0 : Real))
      (𝓝 suzukiCosineRegularConstant) := by
  have hprimitive :
      Tendsto (fun s : Real =>
          ∫ t in (0 : Real)..s, suzukiCosineRegularPart t)
        (𝓝[>] (0 : Real)) (𝓝 0) := by
    have hcontinuous :
        ContinuousAt (fun s : Real =>
          ∫ t in (0 : Real)..s, suzukiCosineRegularPart t) 0 :=
      (continuous_suzukiCosineRegularPart.integral_hasStrictDerivAt 0 0).hasDerivAt.continuousAt
    change Tendsto _ (𝓝 (0 : Real) ⊓ 𝓟 (Ioi 0)) (𝓝 0)
    simpa using hcontinuous.tendsto.mono_left inf_le_left
  have hsub :
      Tendsto (fun s : Real =>
          suzukiCosineRegularConstant -
            ∫ t in (0 : Real)..s, suzukiCosineRegularPart t)
        (𝓝[>] (0 : Real)) (𝓝 (suzukiCosineRegularConstant - 0)) :=
    tendsto_const_nhds.sub hprimitive
  simpa only [sub_zero] using hsub.congr'
    (Eventually.of_forall fun s => (suzukiCosineRegularPartial_eq s).symm)

/-- The normalized scalar cutoff before the Fourier-frequency scaling. -/
def suzukiNormalizedCosineIntegralPartial (s R : Real) : Real :=
  Real.log s + ∫ t in s..R, Real.cos t / t

/-- Splitting at one separates the removable near-zero contribution from the
conditionally convergent tail. -/
theorem suzukiNormalizedCosineIntegralPartial_eq
    {s : Real} (hs : 0 < s) {R : Real} (hR : 1 ≤ R) :
    suzukiNormalizedCosineIntegralPartial s R =
      suzukiCosineRegularPartial s + suzukiCosineTailPartialReal R := by
  have hBetweenPos {t : Real} (ht : t ∈ [[s, 1]]) : 0 < t := by
    exact (lt_min hs zero_lt_one).trans_le ht.1
  have hcosLeft :
      IntervalIntegrable (fun t : Real => Real.cos t / t) volume s 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (Real.continuous_cos.continuousAt.div continuousAt_id
      (hBetweenPos ht).ne').continuousWithinAt
  have hinvLeft :
      IntervalIntegrable (fun t : Real => 1 / t) volume s 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (continuousAt_const.div continuousAt_id
      (hBetweenPos ht).ne').continuousWithinAt
  have hregularLeft :=
    continuous_suzukiCosineRegularPart.intervalIntegrable (μ := volume) s 1
  have hdecompose :
      (∫ t in s..1, Real.cos t / t) =
        suzukiCosineRegularPartial s + ∫ t in s..1, 1 / t := by
    unfold suzukiCosineRegularPartial
    rw [← intervalIntegral.integral_add hregularLeft hinvLeft]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t ≠ 0 := (hBetweenPos ht).ne'
    unfold suzukiCosineRegularPart
    field_simp
    ring
  have hinv : (∫ t in s..1, 1 / t) = -Real.log s := by
    calc
      (∫ t in s..1, 1 / t) = Real.log ((1 : Real) / s) := by
        simpa only [one_div] using
          (integral_inv_of_pos hs zero_lt_one)
      _ = -Real.log s := by
        rw [show (1 : Real) / s = s⁻¹ by simp]
        exact Real.log_inv s
  have hcosRight :
      IntervalIntegrable (fun t : Real => Real.cos t / t) volume 1 R :=
    intervalIntegrable_cos_div_of_one_le (le_refl (1 : Real)) hR
  have hadd := intervalIntegral.integral_add_adjacent_intervals hcosLeft hcosRight
  unfold suzukiNormalizedCosineIntegralPartial suzukiCosineTailPartialReal
  rw [← hadd, hdecompose, hinv]
  ring

/-- Below one, the logarithmic singularity cancels against the integral of
`1/t`, leaving only the endpoint logarithm and the regular part. -/
theorem suzukiNormalizedCosineIntegralPartial_eq_log_add_regular
    {s T : Real} (hs : 0 < s) (hsT : s ≤ T) :
    suzukiNormalizedCosineIntegralPartial s T =
      Real.log T + ∫ t in s..T, suzukiCosineRegularPart t := by
  have hT : 0 < T := hs.trans_le hsT
  have hregular := continuous_suzukiCosineRegularPart.intervalIntegrable
    (μ := volume) s T
  have hinv : IntervalIntegrable (fun t : Real => 1 / t) volume s T := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htpos : 0 < t := by
      rw [uIcc_of_le hsT] at ht
      exact hs.trans_le ht.1
    exact (continuousAt_const.div continuousAt_id htpos.ne').continuousWithinAt
  have hdecompose :
      (∫ t in s..T, Real.cos t / t) =
        (∫ t in s..T, suzukiCosineRegularPart t) +
          ∫ t in s..T, 1 / t := by
    rw [← intervalIntegral.integral_add hregular hinv]
    apply intervalIntegral.integral_congr
    intro t ht
    have htpos : 0 < t := by
      rw [uIcc_of_le hsT] at ht
      exact hs.trans_le ht.1
    unfold suzukiCosineRegularPart
    field_simp
    ring
  have hinvValue :
      (∫ t in s..T, 1 / t) = Real.log T - Real.log s := by
    calc
      (∫ t in s..T, 1 / t) = Real.log (T / s) := by
        simpa only [one_div] using
          (integral_inv_of_pos hs hT)
      _ = Real.log T - Real.log s := Real.log_div hT.ne' hs.ne'
  unfold suzukiNormalizedCosineIntegralPartial
  rw [hdecompose, hinvValue]
  ring

/-- Uniform scalar control in the geometry generated by a positive frequency
scale: `s ≤ k ≤ T`.  This is the domination estimate needed before passing
the reciprocal-kernel Fourier pairing to the joint cutoff limit. -/
theorem abs_suzukiNormalizedCosineIntegralPartial_le
    {s T k : Real} (hs : 0 < s) (hsT : s ≤ T)
    (hsk : s ≤ k) (hkT : k ≤ T) :
    abs (suzukiNormalizedCosineIntegralPartial s T) ≤
      4 + abs (Real.log k) := by
  have hk : 0 < k := hs.trans_le hsk
  by_cases hsOne : s ≤ 1
  · by_cases hOneT : 1 ≤ T
    · rw [suzukiNormalizedCosineIntegralPartial_eq hs hOneT]
      calc
        abs (suzukiCosineRegularPartial s +
            suzukiCosineTailPartialReal T) ≤
            abs (suzukiCosineRegularPartial s) +
              abs (suzukiCosineTailPartialReal T) := abs_add_le _ _
        _ ≤ 1 / 2 + 3 := by
          gcongr
          · unfold suzukiCosineRegularPartial
            exact abs_integral_suzukiCosineRegularPart_le_half hs.le hsOne
              (le_refl (1 : Real))
          · exact abs_suzukiCosineTailPartialReal_le_three hOneT
        _ ≤ 4 + abs (Real.log k) := by
          nlinarith [abs_nonneg (Real.log k)]
    · have hTOne : T ≤ 1 := le_of_not_ge hOneT
      rw [suzukiNormalizedCosineIntegralPartial_eq_log_add_regular hs hsT]
      have hlogT : Real.log T ≤ 0 :=
        Real.log_nonpos (hs.trans_le hsT).le hTOne
      have hlogK : Real.log k ≤ 0 :=
        hlogT.trans' (Real.log_le_log hk hkT)
      have hlogAbs : abs (Real.log T) ≤ abs (Real.log k) := by
        rw [abs_of_nonpos hlogT, abs_of_nonpos hlogK]
        exact neg_le_neg (Real.log_le_log hk hkT)
      calc
        abs (Real.log T +
            ∫ t in s..T, suzukiCosineRegularPart t) ≤
            abs (Real.log T) +
              abs (∫ t in s..T, suzukiCosineRegularPart t) := abs_add_le _ _
        _ ≤ abs (Real.log k) + 1 / 2 := by
          gcongr
          exact abs_integral_suzukiCosineRegularPart_le_half
            hs.le hsT hTOne
        _ ≤ 4 + abs (Real.log k) := by linarith
  · have hOneS : 1 ≤ s := le_of_not_ge hsOne
    have htail :
        abs (∫ t in s..T, Real.cos t / t) ≤ 3 := by
      have hraw := abs_integral_cos_div_le hOneS hsT
      have hthree : 3 / s ≤ 3 := by
        have hspos : 0 < s := hs
        apply (div_le_iff₀ hspos).2
        nlinarith
      exact hraw.trans hthree
    have hlogS : 0 ≤ Real.log s := Real.log_nonneg hOneS
    have hlogK : 0 ≤ Real.log k :=
      hlogS.trans (Real.log_le_log hs hsk)
    unfold suzukiNormalizedCosineIntegralPartial
    calc
      abs (Real.log s + ∫ t in s..T, Real.cos t / t) ≤
          abs (Real.log s) +
            abs (∫ t in s..T, Real.cos t / t) := abs_add_le _ _
      _ ≤ abs (Real.log k) + 3 := by
        rw [abs_of_nonneg hlogS, abs_of_nonneg hlogK]
        gcongr
      _ ≤ 4 + abs (Real.log k) := by linarith

/-- The unscaled normalized cosine integral converges jointly in its lower
and upper cutoffs. -/
theorem tendsto_suzukiNormalizedCosineIntegralPartial :
    Tendsto
      (fun p : Real × Real =>
        suzukiNormalizedCosineIntegralPartial p.1 p.2)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (suzukiCosineRegularConstant + suzukiCosineTailConstant)) := by
  have hregular :
      Tendsto (fun p : Real × Real => suzukiCosineRegularPartial p.1)
        (𝓝[>] (0 : Real) ×ˢ atTop) (𝓝 suzukiCosineRegularConstant) :=
    tendsto_suzukiCosineRegularPartial.comp tendsto_fst
  have htail :
      Tendsto (fun p : Real × Real => suzukiCosineTailPartialReal p.2)
        (𝓝[>] (0 : Real) ×ˢ atTop) (𝓝 suzukiCosineTailConstant) :=
    tendsto_suzukiCosineTailPartialReal.comp tendsto_snd
  have hsum := hregular.add htail
  apply hsum.congr'
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin,
    tendsto_snd.eventually (eventually_ge_atTop 1)] with p hp hR
  exact (suzukiNormalizedCosineIntegralPartial_eq hp hR).symm

/-- Positive dilation converts the frequency-scaled cosine quotient to the
unscaled quotient without a Jacobian residue. -/
theorem integral_cos_mul_div_eq_dilated
    {k ε R : Real} (hk : k ≠ 0) :
    (∫ t in ε..R, Real.cos (k * t) / t) =
      ∫ u in k * ε..k * R, Real.cos u / u := by
  have hpointwise (t : Real) :
      Real.cos (k * t) / t =
        k * (Real.cos (k * t) / (k * t)) := by
    by_cases ht : t = 0
    · simp [ht]
    · field_simp
  calc
    (∫ t in ε..R, Real.cos (k * t) / t) =
        ∫ t in ε..R, k * (Real.cos (k * t) / (k * t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpointwise t
    _ = k * ∫ t in ε..R, Real.cos (k * t) / (k * t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in k * ε..k * R, Real.cos u / u := by
      simpa only [smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left
          (fun u : Real => Real.cos u / u) k (a := ε) (b := R))

/-- The absolute-frequency dilation agrees with Mathlib's Fourier
normalization because cosine is even. -/
theorem integral_cos_fourierFrequency_div_eq_dilated
    {ξ : Real} (hξ : ξ ≠ 0) (ε R : Real) :
    (∫ t in ε..R, Real.cos (2 * Real.pi * t * ξ) / t) =
      ∫ u in (2 * Real.pi * |ξ|) * ε..(2 * Real.pi * |ξ|) * R,
        Real.cos u / u := by
  let k : Real := 2 * Real.pi * |ξ|
  have hk : k ≠ 0 := by
    dsimp [k]
    positivity
  have hcos (t : Real) :
      Real.cos (2 * Real.pi * t * ξ) = Real.cos (k * t) := by
    by_cases hξnonneg : 0 ≤ ξ
    · dsimp [k]
      rw [abs_of_nonneg hξnonneg]
      congr 1
      ring
    · have hξneg : ξ < 0 := lt_of_not_ge hξnonneg
      dsimp [k]
      rw [abs_of_neg hξneg]
      rw [show 2 * Real.pi * -ξ * t =
          -(2 * Real.pi * t * ξ) by ring, Real.cos_neg]
  calc
    (∫ t in ε..R, Real.cos (2 * Real.pi * t * ξ) / t) =
        ∫ t in ε..R, Real.cos (k * t) / t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change Real.cos (2 * Real.pi * t * ξ) / t = Real.cos (k * t) / t
      rw [hcos t]
    _ = ∫ u in k * ε..k * R, Real.cos u / u :=
      integral_cos_mul_div_eq_dilated hk

/-- The renormalized reciprocal-kernel multiplier has a uniform logarithmic
frequency majorant throughout the eventual cutoff region. -/
theorem abs_suzukiRenormalizedCutoffMultiplier_le
    {ε R ξ : Real} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hR : 1 ≤ R) (hξ : ξ ≠ 0) :
    abs (suzukiRenormalizedCutoffMultiplier ε R ξ) ≤
      8 + 4 * abs (Real.log (2 * Real.pi * |ξ|)) := by
  let k : Real := 2 * Real.pi * |ξ|
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hs : 0 < k * ε := mul_pos hk hε
  have hsT : k * ε ≤ k * R := by
    gcongr
    exact hεOne.trans hR
  have hsk : k * ε ≤ k := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hεOne hk.le
  have hkT : k ≤ k * R := by
    nth_rewrite 1 [← mul_one k]
    gcongr
  have hnormalized :=
    abs_suzukiNormalizedCosineIntegralPartial_le hs hsT hsk hkT
  have hidentity :
      suzukiRenormalizedCutoffMultiplier ε R ξ =
        -2 * suzukiNormalizedCosineIntegralPartial
            (k * ε) (k * R) + 2 * Real.log k := by
    unfold suzukiRenormalizedCutoffMultiplier
      suzukiReciprocalCutoffCosineMultiplier
      suzukiNormalizedCosineIntegralPartial
    rw [integral_cos_fourierFrequency_div_eq_dilated hξ]
    rw [Real.log_mul hk.ne' hε.ne']
    dsimp [k]
    ring
  rw [hidentity]
  calc
    abs (-2 * suzukiNormalizedCosineIntegralPartial (k * ε) (k * R) +
        2 * Real.log k) ≤
        2 * abs (suzukiNormalizedCosineIntegralPartial (k * ε) (k * R)) +
          2 * abs (Real.log k) := by
      calc
        abs (-2 * suzukiNormalizedCosineIntegralPartial (k * ε) (k * R) +
            2 * Real.log k) ≤
            abs (-2 * suzukiNormalizedCosineIntegralPartial (k * ε) (k * R)) +
              abs (2 * Real.log k) := abs_add_le _ _
        _ = 2 * abs (suzukiNormalizedCosineIntegralPartial (k * ε) (k * R)) +
              2 * abs (Real.log k) := by simp [abs_mul]
    _ ≤ 2 * (4 + abs (Real.log k)) + 2 * abs (Real.log k) := by
      gcongr
    _ = 8 + 4 * abs (Real.log (2 * Real.pi * |ξ|)) := by
      dsimp [k]
      ring

/-- Rewriting the logarithmic majorant in terms of the exact source weight
makes its integrability immediate on Schwartz Fourier data. -/
theorem abs_suzukiRenormalizedCutoffMultiplier_le_sourceWeight
    {ε R ξ : Real} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hR : 1 ≤ R) (hξ : ξ ≠ 0) :
    abs (suzukiRenormalizedCutoffMultiplier ε R ξ) ≤
      8 + 4 *
        (abs (suzukiSourceLogFourierWeight ξ) +
          abs Real.eulerMascheroniConstant) := by
  have hbase :=
    abs_suzukiRenormalizedCutoffMultiplier_le hε hεOne hR hξ
  have hlog :
      Real.log (2 * Real.pi * |ξ|) =
        suzukiSourceLogFourierWeight ξ - Real.eulerMascheroniConstant := by
    unfold suzukiSourceLogFourierWeight
    ring
  rw [hlog] at hbase
  exact hbase.trans (by
    gcongr
    exact abs_sub _ _)

/-- The one remaining classical constant identification.  It is exactly the
cosine-integral constant formula and contains no quadratic-form data. -/
def SuzukiCosineIntegralConstantIdentity : Prop :=
  suzukiCosineRegularConstant + suzukiCosineTailConstant =
    -Real.eulerMascheroniConstant

/-- The sole classical constant evaluation implies the exact joint cutoff
asymptotic used by the reciprocal-kernel proof. -/
theorem suzukiCosineIntegralAsymptotic_of_constantIdentity
    (hconstant : SuzukiCosineIntegralConstantIdentity) :
    SuzukiCosineIntegralAsymptotic := by
  intro ξ hξ
  let k : Real := 2 * Real.pi * |ξ|
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hscaleZero :
      Tendsto (fun s : Real => k * s) (𝓝[>] (0 : Real))
        (𝓝[>] (0 : Real)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hid : Tendsto (fun s : Real => s) (𝓝[>] (0 : Real)) (𝓝 0) :=
        tendsto_id.mono_right inf_le_left
      simpa using tendsto_const_nhds.mul hid
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hk hs
  have hscaleTop :
      Tendsto (fun R : Real => k * R) atTop atTop :=
    tendsto_id.const_mul_atTop hk
  have hscale :
      Tendsto (fun p : Real × Real => (k * p.1, k * p.2))
        (𝓝[>] (0 : Real) ×ˢ atTop)
        (𝓝[>] (0 : Real) ×ˢ atTop) :=
    (hscaleZero.comp tendsto_fst).prodMk (hscaleTop.comp tendsto_snd)
  have hnormalized :=
    tendsto_suzukiNormalizedCosineIntegralPartial.comp hscale
  change suzukiCosineRegularConstant + suzukiCosineTailConstant =
    -Real.eulerMascheroniConstant at hconstant
  rw [hconstant] at hnormalized
  have htransformed :
      Tendsto
        (fun p : Real × Real =>
          -2 * suzukiNormalizedCosineIntegralPartial
              (k * p.1) (k * p.2) +
            2 * Real.log k)
        (𝓝[>] (0 : Real) ×ˢ atTop)
        (𝓝 (-2 * (-Real.eulerMascheroniConstant) +
          2 * Real.log k)) := by
    exact (hnormalized.const_mul (-2)).add_const (2 * Real.log k)
  have hlimit :
      -2 * (-Real.eulerMascheroniConstant) + 2 * Real.log k =
        2 * suzukiSourceLogFourierWeight ξ := by
    unfold suzukiSourceLogFourierWeight
    dsimp [k]
    ring
  rw [hlimit] at htransformed
  apply htransformed.congr'
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
  unfold suzukiRenormalizedCutoffMultiplier
    suzukiReciprocalCutoffCosineMultiplier
    suzukiNormalizedCosineIntegralPartial
  rw [integral_cos_fourierFrequency_div_eq_dilated hξ]
  rw [Real.log_mul hk.ne' hp.ne']
  dsimp [k]
  ring

end

end M100
end Experiments
end RiemannHypothesisProject
