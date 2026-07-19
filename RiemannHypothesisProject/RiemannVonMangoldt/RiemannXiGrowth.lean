import Mathlib.MeasureTheory.Integral.Bochner.Set
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXi

/-!
# Growth estimates for Riemann's xi function

This file starts the finite-order input for the xi/Jensen zero-counting route.
The first ingredient is a global exponential bound for the modified theta
kernel on `[1, ∞)`, obtained from Mathlib's exponential theta-tail estimate
and compactness on the finite initial interval.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Asymptotics Filter MeasureTheory Set

local instance : NormedSpace ℂ ℂ := RCLike.innerProductSpace.toNormedSpace

/-- The strong theta kernel whose Mellin transform is Mathlib's entire
pole-subtracted completed zeta. -/
def riemannThetaKernel : ℝ → ℂ :=
  (HurwitzZeta.hurwitzEvenFEPair 0).f_modif

/-- On the large half-line, the modified kernel is the usual theta tail. -/
theorem riemannThetaKernel_eq_of_one_lt {x : ℝ} (hx : 1 < x) :
    riemannThetaKernel x = (HurwitzZeta.evenKernel 0 x - 1 : ℝ) := by
  simp [riemannThetaKernel, WeakFEPair.f_modif,
    HurwitzZeta.hurwitzEvenFEPair, hx, hx.le]

/-- The self-dual theta functional equation after removal of its constant
terms. -/
theorem riemannThetaKernel_one_div (x : ℝ) (hx : 0 < x) :
    riemannThetaKernel (1 / x) = ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * riemannThetaKernel x := by
  have hself : (HurwitzZeta.hurwitzEvenFEPair 0).g_modif =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif := by
    ext y
    simp [WeakFEPair.g_modif, WeakFEPair.f_modif,
      HurwitzZeta.hurwitzEvenFEPair,
      HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  have hfe := (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_FE x hx
  rw [hself] at hfe
  simpa [riemannThetaKernel, HurwitzZeta.hurwitzEvenFEPair] using
    hfe

/-- The modified theta kernel occurring in Mathlib's Mellin construction of
`completedRiemannZeta₀` has a uniform exponential bound on `[1, ∞)`.

This is the globalized form of
`HurwitzZeta.isBigO_atTop_evenKernel_sub`; the finite initial interval is
absorbed using continuity and compactness. -/
theorem exists_riemannThetaTail_global_exp_bound :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖HurwitzZeta.evenKernel 0 x - 1‖ ≤ C * Real.exp (-p * x) := by
  obtain ⟨p, hp, htail⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub 0
  obtain ⟨c, hc⟩ := htail.bound
  rw [eventually_atTop] at hc
  obtain ⟨X₀, hX₀⟩ := hc
  let X := max 1 X₀
  have hX_one : 1 ≤ X := le_max_left _ _
  have hX_tail : X₀ ≤ X := le_max_right _ _
  let q : ℝ → ℝ := fun x ↦ ‖HurwitzZeta.evenKernel 0 x - 1‖ / Real.exp (-p * x)
  have hq_cont : ContinuousOn q (Icc 1 X) := by
    apply ContinuousOn.div
    · exact ((HurwitzZeta.continuousOn_evenKernel 0).mono (fun x hx ↦ by
        exact zero_lt_one.trans_le hx.1)).sub continuousOn_const |>.norm
    · fun_prop
    · intro x hx
      exact (Real.exp_pos _).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hq_cont
  let C := max 1 (max c M)
  refine ⟨p, C, hp, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  by_cases hfinite : x ≤ X
  · have hqx : q x ≤ M := hM ⟨x, ⟨hx, hfinite⟩, rfl⟩
    have hqxC : q x ≤ C := hqx.trans <|
      (le_max_right c M).trans (le_max_right 1 (max c M))
    exact (div_le_iff₀ (Real.exp_pos (-p * x))).mp hqxC
  · have hxX : X ≤ x := le_of_not_ge hfinite
    have hcx := hX₀ x (hX_tail.trans hxX)
    have hcx' : ‖HurwitzZeta.evenKernel 0 x - 1‖ ≤ c * Real.exp (-p * x) := by
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hcx
    exact hcx'.trans <| mul_le_mul_of_nonneg_right
      ((le_max_left c M).trans (le_max_right 1 (max c M))) (Real.exp_pos _).le

/-- The preceding real theta-tail estimate, transferred to the exact complex
kernel used by `WeakFEPair.Λ₀`. -/
theorem exists_riemannThetaKernel_global_exp_bound :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaKernel x‖ ≤ C * Real.exp (-p * x) := by
  obtain ⟨p, C, hp, hC, hbound⟩ := exists_riemannThetaTail_global_exp_bound
  refine ⟨p, C, hp, hC, fun x hx ↦ ?_⟩
  rcases hx.eq_or_lt with rfl | hx
  · simp [riemannThetaKernel, WeakFEPair.f_modif]
    positivity
  · rw [riemannThetaKernel_eq_of_one_lt hx]
    simpa only [Complex.norm_real] using hbound x hx.le

/-- Folding the small-
`x` part of the theta Mellin integral onto `[1, ∞)`. This is the analytic
normalization step that makes a uniform sphere bound possible: both terms now
meet the same exponentially decaying large-
`x` kernel. -/
theorem mellin_riemannThetaKernel_small_eq_large (s : ℂ) :
    mellin ((Ioo 0 1).indicator riemannThetaKernel) s =
      ∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ ((1 / 2 : ℂ) - s - 1) * riemannThetaKernel x := by
  let g : ℝ → ℂ := (Ioo 0 1).indicator riemannThetaKernel
  have hinv := mellin_comp_inv g (-s)
  simp only [neg_neg] at hinv
  rw [← hinv]
  unfold mellin
  simp only [smul_eq_mul]
  calc
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (-s - 1) * g x⁻¹) =
        ∫ x : ℝ in Ioi 0, (Ioi 1).indicator
          (fun x : ℝ ↦ (x : ℂ) ^ ((1 / 2 : ℂ) - s - 1) *
            riemannThetaKernel x) x := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
      by_cases h1x : 1 < x
      · have hxinv : x⁻¹ ∈ Ioo (0 : ℝ) 1 :=
          ⟨inv_pos.mpr hx, (inv_lt_one₀ hx).mpr h1x⟩
        rw [show g x⁻¹ = riemannThetaKernel x⁻¹ by
          simp [g, hxinv]]
        rw [show (Ioi (1 : ℝ)).indicator
            (fun y : ℝ ↦ (y : ℂ) ^ ((1 / 2 : ℂ) - s - 1) *
              riemannThetaKernel y) x =
            (x : ℂ) ^ ((1 / 2 : ℂ) - s - 1) * riemannThetaKernel x by
          simp [h1x]]
        rw [← one_div, riemannThetaKernel_one_div x hx]
        rw [Complex.ofReal_cpow hx.le]
        norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
        rw [← mul_assoc, ← Complex.cpow_add (-s - 1) (1 / 2 : ℂ)
          (Complex.ofReal_ne_zero.mpr hx.ne')]
        congr 2
        ring
      · have hxle : x ≤ 1 := le_of_not_gt h1x
        have hxinv : x⁻¹ ∉ Ioo (0 : ℝ) 1 := fun h ↦
          (not_lt_of_ge ((one_le_inv₀ hx).mpr hxle)) h.2
        simp [g, hxinv, h1x]
    _ = ∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ ((1 / 2 : ℂ) - s - 1) * riemannThetaKernel x := by
      rw [setIntegral_indicator measurableSet_Ioi]
      rw [inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

/-- Standard folded Mellin representation of the pole-subtracted completed
zeta kernel. Both complex powers are integrated against the same exponential
theta tail on `[1, ∞)`. -/
theorem mellin_riemannThetaKernel_eq_integral_Ioi (s : ℂ) :
    mellin riemannThetaKernel s =
      ∫ x : ℝ in Ioi 1,
        ((x : ℂ) ^ (s - 1) + (x : ℂ) ^ ((1 / 2 : ℂ) - s - 1)) *
          riemannThetaKernel x := by
  let F : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (s - 1) * riemannThetaKernel x
  let G : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ ((1 / 2 : ℂ) - s - 1) * riemannThetaKernel x
  have hF : IntegrableOn F (Ioi 0) := by
    have h := ((HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin s).1
    rw [MellinConvergent] at h
    simpa only [F, riemannThetaKernel, WeakFEPair.toStrongFEPair,
      smul_eq_mul] using h
  have hG : IntegrableOn G (Ioi 0) := by
    have h := ((HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin
      ((1 / 2 : ℂ) - s)).1
    rw [MellinConvergent] at h
    simpa only [G, riemannThetaKernel, WeakFEPair.toStrongFEPair,
      smul_eq_mul] using h
  have hsmall : mellin ((Ioo 0 1).indicator riemannThetaKernel) s =
      ∫ x : ℝ in Ioc 0 1, F x := by
    unfold mellin
    simp only [smul_eq_mul]
    calc
      (∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ (s - 1) * (Ioo 0 1).indicator riemannThetaKernel x) =
          ∫ x : ℝ in Ioi 0, (Ioo 0 1).indicator F x := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
        simp [F, indicator]
      _ = ∫ x : ℝ in Ioo 0 1, F x := by
        rw [setIntegral_indicator measurableSet_Ioo]
        rw [inter_eq_right.mpr Ioo_subset_Ioi_self]
      _ = ∫ x : ℝ in Ioc 0 1, F x := integral_Ioc_eq_integral_Ioo.symm
  calc
    mellin riemannThetaKernel s = ∫ x : ℝ in Ioi 0, F x := by rfl
    _ = (∫ x : ℝ in Ioc 0 1, F x) + ∫ x : ℝ in Ioi 1, F x := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set Ioc_subset_Ioi_self)
        (hF.mono_set (Ioi_subset_Ioi zero_le_one))]
      rw [Ioc_union_Ioi_eq_Ioi zero_le_one]
    _ = (∫ x : ℝ in Ioi 1, G x) + ∫ x : ℝ in Ioi 1, F x := by
      rw [← hsmall, mellin_riemannThetaKernel_small_eq_large]
    _ = ∫ x : ℝ in Ioi 1, F x + G x := by
      rw [add_comm, integral_add
        (hF.mono_set (Ioi_subset_Ioi zero_le_one))
        (hG.mono_set (Ioi_subset_Ioi zero_le_one))]
    _ = ∫ x : ℝ in Ioi 1,
        ((x : ℂ) ^ (s - 1) + (x : ℂ) ^ ((1 / 2 : ℂ) - s - 1)) *
          riemannThetaKernel x := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
      simp only [F, G]
      ring

/-- The folded large-half-line integral for Mathlib's
`completedRiemannZeta₀`. -/
theorem completedRiemannZeta₀_eq_integral_Ioi (s : ℂ) :
    completedRiemannZeta₀ s =
      (∫ x : ℝ in Ioi 1,
        ((x : ℂ) ^ (s / 2 - 1) +
          (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x) / 2 := by
  unfold completedRiemannZeta₀ HurwitzZeta.completedHurwitzZetaEven₀
    WeakFEPair.Λ₀
  change mellin riemannThetaKernel (s / 2) / 2 = _
  rw [mellin_riemannThetaKernel_eq_integral_Ioi]
  congr 3
  funext x
  congr 3
  ring

/-- A scaled `2uv ≤ u² + v²` estimate, arranged for the square-root
majorant used in the theta integral. -/
theorem two_mul_mul_sqrt_le_sq_div_add_mul
    {a q x : ℝ} (hq : 0 < q) (hx : 0 ≤ x) :
    2 * a * Real.sqrt x ≤ a ^ 2 / q + q * x := by
  rw [show a ^ 2 / q + q * x = (a ^ 2 + q ^ 2 * x) / q by
    field_simp]
  rw [le_div_iff₀ hq]
  nlinarith [sq_nonneg (a - q * Real.sqrt x), Real.sq_sqrt hx]

/-- The optimized cubic absorption behind the order-`3 / 2` theta-Mellin
bound.  The nonnegative factor `(y - b)^2 * (y + 2*b)`, with
`b = sqrt (2*a/p)`, gives the sharp power of `a` needed downstream. -/
theorem three_mul_sub_cubic_le_rpow_three_halves
    {a p y : ℝ} (ha : 0 ≤ a) (hp : 0 < p) (hy : 0 ≤ y) :
    3 * a * y - (p / 2) * y ^ 3 ≤
      2 * Real.sqrt (2 / p) * a ^ (3 / 2 : ℝ) := by
  let b : ℝ := Real.sqrt (2 * a / p)
  have hab : 0 ≤ 2 * a / p := by positivity
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = 2 * a / p := Real.sq_sqrt hab
  have hp_b2 : p * b ^ 2 = 2 * a := by
    rw [hb2]
    field_simp
  have hp_b3 : p * b ^ 3 = 2 * a * b := by
    calc
      p * b ^ 3 = (p * b ^ 2) * b := by ring
      _ = 2 * a * b := by rw [hp_b2]
  have hpoly : 0 ≤ (y - b) ^ 2 * (y + 2 * b) := by positivity
  have hopt : 3 * a * y - (p / 2) * y ^ 3 ≤ 2 * a * b := by
    nlinarith
  have hb : b = Real.sqrt (2 / p) * Real.sqrt a := by
    dsimp [b]
    rw [show 2 * a / p = (2 / p) * a by ring]
    exact Real.sqrt_mul (by positivity) a
  have ha_sqrt : a * Real.sqrt a = a ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      a * a ^ (1 / 2 : ℝ) = a ^ (1 : ℝ) * a ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = a ^ ((1 : ℝ) + 1 / 2) :=
        (Real.rpow_add_of_nonneg ha (by positivity) (by positivity)).symm
      _ = a ^ (3 / 2 : ℝ) := by norm_num
  calc
    3 * a * y - (p / 2) * y ^ 3 ≤ 2 * a * b := hopt
    _ = 2 * Real.sqrt (2 / p) * a ^ (3 / 2 : ℝ) := by
      rw [hb, ← ha_sqrt]
      ring

/-- Exponential absorption with subquadratic dependence on the variable
power.  This is the substantive improvement over the square-root estimate
below: `log x ≤ 3*x^(1/3)` turns the optimization into a cubic one. -/
theorem mul_log_sub_mul_le_rpow_three_halves_sub_mul
    {a p x : ℝ} (ha : 0 ≤ a) (hp : 0 < p) (hx : 1 ≤ x) :
    a * Real.log x - p * x ≤
      2 * Real.sqrt (2 / p) * a ^ (3 / 2 : ℝ) - (p / 2) * x := by
  let y : ℝ := x ^ (1 / 3 : ℝ)
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx0 _
  have hlog := Real.log_le_rpow_div hx0 (show 0 < (1 / 3 : ℝ) by norm_num)
  have hlog' : Real.log x ≤ 3 * y := by
    dsimp [y]
    convert hlog using 1
    all_goals ring
  have hy3 : y ^ 3 = x := by
    dsimp [y]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx0]
    norm_num
  have hamul : a * Real.log x ≤ a * (3 * y) :=
    mul_le_mul_of_nonneg_left hlog' ha
  have hopt := three_mul_sub_cubic_le_rpow_three_halves ha hp hy0
  rw [hy3] at hopt
  nlinarith

/-- Pointwise order-`3 / 2` exponential majorant for the variable power in
the folded theta integral. -/
theorem rpow_mul_exp_neg_mul_le_exp_rpow_three_halves_mul_exp
    {a p x : ℝ} (ha : 0 ≤ a) (hp : 0 < p) (hx : 1 ≤ x) :
    x ^ a * Real.exp (-p * x) ≤
      Real.exp (2 * Real.sqrt (2 / p) * a ^ (3 / 2 : ℝ)) *
        Real.exp (-(p / 2) * x) := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx)]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_log_sub_mul_le_rpow_three_halves_sub_mul ha hp hx
  nlinarith

/-- Optimal logarithmic absorption for the theta-Mellin integrand. Splitting
`p = p/2 + p/2` and applying `log u ≤ u - 1` at
`u = (p/2)*x/a` leaves a fixed exponential tail and only `a*log a`
dependence in the parameter. -/
theorem mul_log_sub_mul_le_mul_log_abs_sub_mul
    {a p x : ℝ} (ha : 0 < a) (hp : 0 < p) (hx : 0 < x) :
    a * Real.log x - p * x ≤
      a * (Real.log a + |Real.log (p / 2)|) - (p / 2) * x := by
  let q : ℝ := p / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hu : 0 < q * x / a := by positivity
  have hlog := Real.log_le_sub_one_of_pos hu
  have hlog_eq : Real.log (q * x / a) =
      Real.log q + Real.log x - Real.log a := by
    rw [Real.log_div (mul_ne_zero hq.ne' hx.ne') ha.ne',
      Real.log_mul hq.ne' hx.ne']
  rw [hlog_eq] at hlog
  have hamul := mul_le_mul_of_nonneg_left hlog ha.le
  have hopt : a * Real.log x - q * x ≤
      a * (Real.log a - Real.log q) - a := by
    have haq : a * (q * x / a - 1) = q * x - a := by
      field_simp
    rw [haq] at hamul
    nlinarith
  have hneglog : -Real.log q ≤ |Real.log q| := neg_le_abs _
  have habs : a * (Real.log a - Real.log q) - a ≤
      a * (Real.log a + |Real.log q|) := by
    nlinarith [mul_le_mul_of_nonneg_left hneglog ha.le]
  dsimp [q] at hopt habs ⊢
  nlinarith

/-- Pointwise order-one exponential majorant for the variable power in the
folded theta integral. -/
theorem rpow_mul_exp_neg_mul_le_exp_mul_log_abs_mul_exp
    {a p x : ℝ} (ha : 0 < a) (hp : 0 < p) (hx : 1 ≤ x) :
    x ^ a * Real.exp (-p * x) ≤
      Real.exp (a * (Real.log a + |Real.log (p / 2)|)) *
        Real.exp (-(p / 2) * x) := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx)]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_log_sub_mul_le_mul_log_abs_sub_mul ha hp
    (zero_lt_one.trans_le hx)
  nlinarith

/-- Exponential absorption for the variable power in the folded theta
integral. The loss `2 a² / p` is deliberately coarse but gives a clean
finite-order bound without invoking Stirling's formula. -/
theorem mul_log_sub_mul_le_sq_sub_mul
    {a p x : ℝ} (ha : 0 ≤ a) (hp : 0 < p) (hx : 1 ≤ x) :
    a * Real.log x - p * x ≤ 2 * a ^ 2 / p - (p / 2) * x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hlog := Real.log_le_rpow_div hx0 (show 0 < (1 / 2 : ℝ) by norm_num)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hlog' : Real.log x ≤ 2 * Real.sqrt x := by
    linarith
  have hamul : a * Real.log x ≤ a * (2 * Real.sqrt x) :=
    mul_le_mul_of_nonneg_left hlog' ha
  have hyoung := two_mul_mul_sqrt_le_sq_div_add_mul
    (a := a) (q := p / 2) (x := x) (by positivity) hx0
  field_simp at hyoung ⊢
  nlinarith

/-- The pointwise exponential majorant used after taking norms of complex
powers. -/
theorem rpow_mul_exp_neg_mul_le_exp_sq_mul_exp
    {a p x : ℝ} (ha : 0 ≤ a) (hp : 0 < p) (hx : 1 ≤ x) :
    x ^ a * Real.exp (-p * x) ≤
      Real.exp (2 * a ^ 2 / p) * Real.exp (-(p / 2) * x) := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx)]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_log_sub_mul_le_sq_sub_mul ha hp hx
  nlinarith

/-- A complex power against the Riemann theta kernel is dominated by a fixed
exponential tail, with quadratic dependence on an upper bound for the real
part of the exponent. -/
theorem norm_cpow_mul_riemannThetaKernel_le
    {w : ℂ} {a p C x : ℝ}
    (ha : 0 ≤ a) (hp : 0 < p) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hw : w.re ≤ a)
    (hkernel : ‖riemannThetaKernel x‖ ≤ C * Real.exp (-p * x)) :
    ‖(x : ℂ) ^ w * riemannThetaKernel x‖ ≤
      C * Real.exp (2 * a ^ 2 / p) * Real.exp (-(p / 2) * x) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
  calc
    x ^ w.re * ‖riemannThetaKernel x‖ ≤
        x ^ a * (C * Real.exp (-p * x)) := by
      gcongr
    _ = C * (x ^ a * Real.exp (-p * x)) := by ring
    _ ≤ C * (Real.exp (2 * a ^ 2 / p) * Real.exp (-(p / 2) * x)) := by
      exact mul_le_mul_of_nonneg_left
        (rpow_mul_exp_neg_mul_le_exp_sq_mul_exp ha hp hx) hC
    _ = C * Real.exp (2 * a ^ 2 / p) * Real.exp (-(p / 2) * x) := by ring

/-- A complex power against the Riemann theta kernel is dominated by a fixed
exponential tail with order-`3 / 2` dependence on the exponent bound. -/
theorem norm_cpow_mul_riemannThetaKernel_le_rpow_three_halves
    {w : ℂ} {a p C x : ℝ}
    (ha : 0 ≤ a) (hp : 0 < p) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hw : w.re ≤ a)
    (hkernel : ‖riemannThetaKernel x‖ ≤ C * Real.exp (-p * x)) :
    ‖(x : ℂ) ^ w * riemannThetaKernel x‖ ≤
      C * Real.exp (2 * Real.sqrt (2 / p) * a ^ (3 / 2 : ℝ)) *
        Real.exp (-(p / 2) * x) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
  calc
    x ^ w.re * ‖riemannThetaKernel x‖ ≤
        x ^ a * (C * Real.exp (-p * x)) := by
      gcongr
    _ = C * (x ^ a * Real.exp (-p * x)) := by ring
    _ ≤ C * (Real.exp (2 * Real.sqrt (2 / p) * a ^ (3 / 2 : ℝ)) *
          Real.exp (-(p / 2) * x)) := by
      exact mul_le_mul_of_nonneg_left
        (rpow_mul_exp_neg_mul_le_exp_rpow_three_halves_mul_exp ha hp hx) hC
    _ = C * Real.exp (2 * Real.sqrt (2 / p) * a ^ (3 / 2 : ℝ)) *
        Real.exp (-(p / 2) * x) := by ring

/-- A complex power against the theta kernel with order-one dependence on the
real-part bound. -/
theorem norm_cpow_mul_riemannThetaKernel_le_mul_log
    {w : ℂ} {a p C x : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hw : w.re ≤ a)
    (hkernel : ‖riemannThetaKernel x‖ ≤ C * Real.exp (-p * x)) :
    ‖(x : ℂ) ^ w * riemannThetaKernel x‖ ≤
      C * Real.exp (a * (Real.log a + |Real.log (p / 2)|)) *
        Real.exp (-(p / 2) * x) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
  calc
    x ^ w.re * ‖riemannThetaKernel x‖ ≤
        x ^ a * (C * Real.exp (-p * x)) := by
      gcongr
    _ = C * (x ^ a * Real.exp (-p * x)) := by ring
    _ ≤ C * (Real.exp (a * (Real.log a + |Real.log (p / 2)|)) *
          Real.exp (-(p / 2) * x)) := by
      exact mul_le_mul_of_nonneg_left
        (rpow_mul_exp_neg_mul_le_exp_mul_log_abs_mul_exp ha hp hx) hC
    _ = C * Real.exp (a * (Real.log a + |Real.log (p / 2)|)) *
        Real.exp (-(p / 2) * x) := by ring

/-- A global order-one bound for the pole-subtracted completed zeta directly
from the optimized folded theta integral. -/
theorem exists_completedRiemannZeta₀_mulLogExp_bound :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤
        C * Real.exp ((‖s‖ + 2) *
          (Real.log (‖s‖ + 2) + |Real.log (p / 2)|)) *
          Real.exp (-(p / 2)) / (p / 2) := by
  obtain ⟨p, C, hp, hC, hkernel⟩ :=
    exists_riemannThetaKernel_global_exp_bound
  refine ⟨p, C, hp, hC, fun s ↦ ?_⟩
  let a : ℝ := ‖s‖ + 2
  let B : ℝ := C * Real.exp
    (a * (Real.log a + |Real.log (p / 2)|))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hC0 : 0 ≤ C := hC.le
  have hw₁ : (s / 2 - 1).re ≤ a := by
    dsimp [a]
    norm_num
    nlinarith [Complex.re_le_norm s, norm_nonneg s]
  have hw₂ : ((1 - s) / 2 - 1).re ≤ a := by
    have hre : -s.re ≤ ‖s‖ := by
      have habs := Complex.abs_re_le_norm s
      exact (neg_le_abs s.re).trans habs
    dsimp [a]
    norm_num
    nlinarith
  have hdom : IntegrableOn
      (fun x : ℝ ↦ 2 * B * Real.exp (-(p / 2) * x)) (Ioi 1) := by
    exact (integrableOn_exp_mul_Ioi (by linarith : -(p / 2) < 0) 1).const_mul _
  have hnorm :
      ‖∫ x : ℝ in Ioi 1,
          ((x : ℂ) ^ (s / 2 - 1) +
            (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x‖ ≤
        ∫ x : ℝ in Ioi 1, 2 * B * Real.exp (-(p / 2) * x) := by
    apply norm_integral_le_of_norm_le hdom
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := hx.le
    have h₁ := norm_cpow_mul_riemannThetaKernel_le_mul_log
      ha hp hC0 hx1 hw₁ (hkernel x hx1)
    have h₂ := norm_cpow_mul_riemannThetaKernel_le_mul_log
      ha hp hC0 hx1 hw₂ (hkernel x hx1)
    calc
      ‖((x : ℂ) ^ (s / 2 - 1) +
          (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x‖ =
          ‖(x : ℂ) ^ (s / 2 - 1) * riemannThetaKernel x +
            (x : ℂ) ^ ((1 - s) / 2 - 1) * riemannThetaKernel x‖ := by
              congr 1
              ring
      _ ≤ ‖(x : ℂ) ^ (s / 2 - 1) * riemannThetaKernel x‖ +
          ‖(x : ℂ) ^ ((1 - s) / 2 - 1) * riemannThetaKernel x‖ := norm_add_le _ _
      _ ≤ B * Real.exp (-(p / 2) * x) + B * Real.exp (-(p / 2) * x) := by
        simpa only [B, mul_assoc] using add_le_add h₁ h₂
      _ = 2 * B * Real.exp (-(p / 2) * x) := by ring
  rw [completedRiemannZeta₀_eq_integral_Ioi, norm_div]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  calc
    ‖∫ x : ℝ in Ioi 1,
        ((x : ℂ) ^ (s / 2 - 1) +
          (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x‖ / 2 ≤
        (∫ x : ℝ in Ioi 1, 2 * B * Real.exp (-(p / 2) * x)) / 2 := by
      gcongr
    _ = B * Real.exp (-(p / 2)) / (p / 2) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (by linarith : -(p / 2) < 0)]
      dsimp [B]
      field_simp
    _ = C * Real.exp ((‖s‖ + 2) *
          (Real.log (‖s‖ + 2) + |Real.log (p / 2)|)) *
        Real.exp (-(p / 2)) / (p / 2) := by rfl

/-- Conventional order-one packaging of the completed-zeta estimate. -/
theorem exists_completedRiemannZeta₀_finiteOrder_mulLog_bound :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤
        K * Real.exp (k * (‖s‖ + 2) * (Real.log (‖s‖ + 2) + 1)) := by
  obtain ⟨p, C, hp, hC, hbound⟩ := exists_completedRiemannZeta₀_mulLogExp_bound
  let D : ℝ := |Real.log (p / 2)|
  let K : ℝ := C * Real.exp (-(p / 2)) / (p / 2)
  let k : ℝ := D + 1
  have hD : 0 ≤ D := abs_nonneg _
  refine ⟨K, k, ?_, ?_, fun s ↦ ?_⟩
  · dsimp [K]
    positivity
  · dsimp [k]
    linarith
  · let a : ℝ := ‖s‖ + 2
    have ha : 2 ≤ a := by
      dsimp [a]
      linarith [norm_nonneg s]
    have hloga : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
    have hexponent : a * (Real.log a + D) ≤
        k * a * (Real.log a + 1) := by
      dsimp [k]
      nlinarith [mul_nonneg hD hloga]
    calc
      ‖completedRiemannZeta₀ s‖ ≤
          C * Real.exp (a * (Real.log a + D)) *
            Real.exp (-(p / 2)) / (p / 2) := by
        simpa [a, D] using hbound s
      _ = K * Real.exp (a * (Real.log a + D)) := by
        dsimp [K]
        ring
      _ ≤ K * Real.exp (k * a * (Real.log a + 1)) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)
      _ = K * Real.exp
          (k * (‖s‖ + 2) * (Real.log (‖s‖ + 2) + 1)) := by rfl

/-- The xi normalization inherits the order-one completed-zeta estimate. -/
theorem exists_riemannXi_polynomial_mulLogExp_bound :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ s : ℂ,
      ‖riemannXi s‖ ≤
        (‖s‖ * (‖s‖ + 1) * K *
          Real.exp (k * (‖s‖ + 2) * (Real.log (‖s‖ + 2) + 1)) + 1) / 2 := by
  obtain ⟨K, k, hK, hk, hbound⟩ :=
    exists_completedRiemannZeta₀_finiteOrder_mulLog_bound
  refine ⟨K, k, hK, hk, fun s ↦ ?_⟩
  have hsub : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    simpa using norm_sub_le s (1 : ℂ)
  unfold riemannXi
  rw [norm_div]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  calc
    ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ / 2 ≤
        (‖s * (s - 1) * completedRiemannZeta₀ s‖ + 1) / 2 := by
      gcongr
      simpa using norm_add_le (s * (s - 1) * completedRiemannZeta₀ s) (1 : ℂ)
    _ = (‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1) / 2 := by
      rw [norm_mul, norm_mul]
    _ ≤ (‖s‖ * (‖s‖ + 1) *
          (K * Real.exp (k * (‖s‖ + 2) *
            (Real.log (‖s‖ + 2) + 1))) + 1) / 2 := by
      gcongr
      exact hbound s
    _ = (‖s‖ * (‖s‖ + 1) * K *
          Real.exp (k * (‖s‖ + 2) * (Real.log (‖s‖ + 2) + 1)) + 1) / 2 := by
      ring

/-- Order-one growth on spheres centered at the Jensen base point `2`. -/
theorem exists_riemannXi_sphere_mulLogExp_bound :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ z ∈ Metric.sphere (2 : ℂ) R,
        ‖riemannXi z‖ ≤
          (R + 2) * (R + 3) * K *
            Real.exp (k * (R + 4) * (Real.log (R + 4) + 1)) + 1 := by
  obtain ⟨K, k, hK, hk, hxi⟩ := exists_riemannXi_polynomial_mulLogExp_bound
  refine ⟨K, k, hK, hk, fun R hR z hz ↦ ?_⟩
  have hdist : dist z (2 : ℂ) = R := Metric.mem_sphere.mp hz
  have hnormsub : ‖z - 2‖ = R := by
    simpa only [dist_eq_norm] using hdist
  have hnorm : ‖z‖ ≤ R + 2 := by
    calc
      ‖z‖ = ‖(z - 2) + 2‖ := by
        congr 1
        ring
      _ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = R + 2 := by
        rw [hnormsub]
        norm_num
  have hnorm1 : ‖z‖ + 1 ≤ R + 3 := by linarith
  have hnorm2 : ‖z‖ + 2 ≤ R + 4 := by linarith
  have hlog : Real.log (‖z‖ + 2) ≤ Real.log (R + 4) :=
    Real.log_le_log (by positivity) hnorm2
  have hmulLog : (‖z‖ + 2) * (Real.log (‖z‖ + 2) + 1) ≤
      (R + 4) * (Real.log (R + 4) + 1) := by
    have hleft : 0 ≤ ‖z‖ + 2 := by positivity
    have hlogleft : 0 ≤ Real.log (‖z‖ + 2) :=
      Real.log_nonneg (by linarith [norm_nonneg z])
    exact mul_le_mul hnorm2 (by linarith) (by linarith) (by linarith)
  have hexp : Real.exp (k * (‖z‖ + 2) * (Real.log (‖z‖ + 2) + 1)) ≤
      Real.exp (k * (R + 4) * (Real.log (R + 4) + 1)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    ‖riemannXi z‖ ≤
        (‖z‖ * (‖z‖ + 1) * K *
          Real.exp (k * (‖z‖ + 2) * (Real.log (‖z‖ + 2) + 1)) + 1) / 2 := hxi z
    _ ≤ ((R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) * (Real.log (R + 4) + 1)) + 1) / 2 := by
      gcongr
    _ ≤ (R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) * (Real.log (R + 4) + 1)) + 1 := by
      have hnonneg : 0 ≤ (R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) * (Real.log (R + 4) + 1)) := by positivity
      linarith

/-- Pure order-one exponential sphere growth for Jensen's inequality. -/
theorem exists_riemannXi_sphere_exp_mulLog_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ z ∈ Metric.sphere (2 : ℂ) R,
        ‖riemannXi z‖ ≤
          Real.exp (A * (R + 4) * (Real.log (R + 4) + 1)) := by
  obtain ⟨K, k, hK, hk, hbound⟩ := exists_riemannXi_sphere_mulLogExp_bound
  let A : ℝ := K + k + 3
  refine ⟨A, by dsimp [A]; positivity, fun R hR z hz ↦ ?_⟩
  let u : ℝ := (R + 4) * (Real.log (R + 4) + 1)
  have hbase : 1 ≤ R + 4 := by linarith
  have hlog0 : 0 ≤ Real.log (R + 4) := Real.log_nonneg hbase
  have hfactor : 1 ≤ Real.log (R + 4) + 1 := by linarith
  have hlinear : R + 4 ≤ u := by
    dsimp [u]
    nlinarith [mul_le_mul_of_nonneg_left hfactor (by linarith : 0 ≤ R + 4)]
  have hu1 : 1 ≤ u := hbase.trans hlinear
  have hR2 : R + 2 ≤ Real.exp u := by
    calc
      R + 2 ≤ u := by linarith
      _ ≤ Real.exp u :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp u)
  have hR3 : R + 3 ≤ Real.exp u := by
    calc
      R + 3 ≤ u := by linarith
      _ ≤ Real.exp u :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp u)
  have hKexp : K ≤ Real.exp (K * u) := by
    calc
      K ≤ K * u := by nlinarith
      _ ≤ Real.exp (K * u) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hpoly : (R + 2) * (R + 3) * K * Real.exp (k * u) ≤
      Real.exp ((K + k + 2) * u) := by
    calc
      (R + 2) * (R + 3) * K * Real.exp (k * u) ≤
          Real.exp u * Real.exp u * Real.exp (K * u) * Real.exp (k * u) := by
        gcongr
      _ = Real.exp ((K + k + 2) * u) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have htwo : (2 : ℝ) ≤ Real.exp u := by
    calc
      (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        norm_num at h ⊢
        exact h
      _ ≤ Real.exp u := Real.exp_le_exp.mpr hu1
  calc
    ‖riemannXi z‖ ≤ (R + 2) * (R + 3) * K *
        Real.exp (k * (R + 4) * (Real.log (R + 4) + 1)) + 1 := hbound R hR z hz
    _ ≤ Real.exp ((K + k + 2) * u) + 1 := by
      have hpoly' : (R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) * (Real.log (R + 4) + 1)) ≤
            Real.exp ((K + k + 2) * u) := by
        rw [show k * (R + 4) * (Real.log (R + 4) + 1) = k * u by
          dsimp [u]
          ring]
        exact hpoly
      linarith
    _ ≤ 2 * Real.exp ((K + k + 2) * u) := by
      have hE : 1 ≤ Real.exp ((K + k + 2) * u) := by
        exact Real.one_le_exp (by positivity)
      linarith
    _ ≤ Real.exp u * Real.exp ((K + k + 2) * u) := by
      gcongr
    _ = Real.exp (A * (R + 4) * (Real.log (R + 4) + 1)) := by
      rw [← Real.exp_add]
      dsimp [A, u]
      congr 1
      ring

/-- A global order-`3 / 2` exponential bound for Mathlib's entire
pole-subtracted completed zeta, obtained directly from the folded theta
integral and the optimized cubic absorption estimate. -/
theorem exists_completedRiemannZeta₀_rpowThreeHalvesExp_bound :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤
        C * Real.exp
          (2 * Real.sqrt (2 / p) * (‖s‖ + 2) ^ (3 / 2 : ℝ)) *
          Real.exp (-(p / 2)) / (p / 2) := by
  obtain ⟨p, C, hp, hC, hkernel⟩ :=
    exists_riemannThetaKernel_global_exp_bound
  refine ⟨p, C, hp, hC, fun s ↦ ?_⟩
  let a : ℝ := ‖s‖ + 2
  let B : ℝ :=
    C * Real.exp (2 * Real.sqrt (2 / p) * a ^ (3 / 2 : ℝ))
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hC0 : 0 ≤ C := hC.le
  have hw₁ : (s / 2 - 1).re ≤ a := by
    dsimp [a]
    norm_num
    nlinarith [Complex.re_le_norm s, norm_nonneg s]
  have hw₂ : ((1 - s) / 2 - 1).re ≤ a := by
    have hre : -s.re ≤ ‖s‖ := by
      have habs := Complex.abs_re_le_norm s
      exact (neg_le_abs s.re).trans habs
    dsimp [a]
    norm_num
    nlinarith
  have hdom : IntegrableOn
      (fun x : ℝ ↦ 2 * B * Real.exp (-(p / 2) * x)) (Ioi 1) := by
    exact (integrableOn_exp_mul_Ioi (by linarith : -(p / 2) < 0) 1).const_mul _
  have hnorm :
      ‖∫ x : ℝ in Ioi 1,
          ((x : ℂ) ^ (s / 2 - 1) +
            (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x‖ ≤
        ∫ x : ℝ in Ioi 1, 2 * B * Real.exp (-(p / 2) * x) := by
    apply norm_integral_le_of_norm_le hdom
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := hx.le
    have h₁ := norm_cpow_mul_riemannThetaKernel_le_rpow_three_halves
      ha hp hC0 hx1 hw₁ (hkernel x hx1)
    have h₂ := norm_cpow_mul_riemannThetaKernel_le_rpow_three_halves
      ha hp hC0 hx1 hw₂ (hkernel x hx1)
    calc
      ‖((x : ℂ) ^ (s / 2 - 1) +
          (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x‖ =
          ‖(x : ℂ) ^ (s / 2 - 1) * riemannThetaKernel x +
            (x : ℂ) ^ ((1 - s) / 2 - 1) * riemannThetaKernel x‖ := by
              congr 1
              ring
      _ ≤ ‖(x : ℂ) ^ (s / 2 - 1) * riemannThetaKernel x‖ +
          ‖(x : ℂ) ^ ((1 - s) / 2 - 1) * riemannThetaKernel x‖ := norm_add_le _ _
      _ ≤ B * Real.exp (-(p / 2) * x) + B * Real.exp (-(p / 2) * x) := by
        simpa only [B, mul_assoc] using add_le_add h₁ h₂
      _ = 2 * B * Real.exp (-(p / 2) * x) := by ring
  rw [completedRiemannZeta₀_eq_integral_Ioi, norm_div]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  calc
    ‖∫ x : ℝ in Ioi 1,
        ((x : ℂ) ^ (s / 2 - 1) +
          (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x‖ / 2 ≤
        (∫ x : ℝ in Ioi 1, 2 * B * Real.exp (-(p / 2) * x)) / 2 := by
      gcongr
    _ = B * Real.exp (-(p / 2)) / (p / 2) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (by linarith : -(p / 2) < 0)]
      dsimp [B]
      field_simp
    _ = C * Real.exp
          (2 * Real.sqrt (2 / p) * (‖s‖ + 2) ^ (3 / 2 : ℝ)) *
        Real.exp (-(p / 2)) / (p / 2) := by rfl

/-- Finite-order packaging of the order-`3 / 2` completed-zeta bound. -/
theorem exists_completedRiemannZeta₀_finiteOrder_rpowThreeHalves_bound :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤
        K * Real.exp (k * (‖s‖ + 2) ^ (3 / 2 : ℝ)) := by
  obtain ⟨p, C, hp, hC, hbound⟩ :=
    exists_completedRiemannZeta₀_rpowThreeHalvesExp_bound
  let K := C * Real.exp (-(p / 2)) / (p / 2)
  let k := 2 * Real.sqrt (2 / p)
  refine ⟨K, k, ?_, ?_, fun s ↦ ?_⟩
  · dsimp [K]
    positivity
  · dsimp [k]
    positivity
  · refine (hbound s).trans_eq ?_
    dsimp [K, k]
    ring

/-- The xi normalization inherits the order-`3 / 2` completed-zeta bound,
with only its defining quadratic polynomial left visible. -/
theorem exists_riemannXi_polynomial_rpowThreeHalvesExp_bound :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ s : ℂ,
      ‖riemannXi s‖ ≤
        (‖s‖ * (‖s‖ + 1) * K *
          Real.exp (k * (‖s‖ + 2) ^ (3 / 2 : ℝ)) + 1) / 2 := by
  obtain ⟨K, k, hK, hk, hbound⟩ :=
    exists_completedRiemannZeta₀_finiteOrder_rpowThreeHalves_bound
  refine ⟨K, k, hK, hk, fun s ↦ ?_⟩
  have hsub : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    simpa using norm_sub_le s (1 : ℂ)
  unfold riemannXi
  rw [norm_div]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  calc
    ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ / 2 ≤
        (‖s * (s - 1) * completedRiemannZeta₀ s‖ + 1) / 2 := by
      gcongr
      simpa using norm_add_le (s * (s - 1) * completedRiemannZeta₀ s) (1 : ℂ)
    _ = (‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1) / 2 := by
      rw [norm_mul, norm_mul]
    _ ≤ (‖s‖ * (‖s‖ + 1) *
          (K * Real.exp (k * (‖s‖ + 2) ^ (3 / 2 : ℝ))) + 1) / 2 := by
      gcongr
      exact hbound s
    _ = (‖s‖ * (‖s‖ + 1) * K *
          Real.exp (k * (‖s‖ + 2) ^ (3 / 2 : ℝ)) + 1) / 2 := by ring

/-- Order-`3 / 2` growth on spheres centered at the nonvanishing Jensen base
point `2`. -/
theorem exists_riemannXi_sphere_rpowThreeHalvesExp_bound :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ z ∈ Metric.sphere (2 : ℂ) R,
        ‖riemannXi z‖ ≤
          (R + 2) * (R + 3) * K *
            Real.exp (k * (R + 4) ^ (3 / 2 : ℝ)) + 1 := by
  obtain ⟨K, k, hK, hk, hxi⟩ :=
    exists_riemannXi_polynomial_rpowThreeHalvesExp_bound
  refine ⟨K, k, hK, hk, fun R hR z hz ↦ ?_⟩
  have hdist : dist z (2 : ℂ) = R := Metric.mem_sphere.mp hz
  have hnormsub : ‖z - 2‖ = R := by
    simpa only [dist_eq_norm] using hdist
  have hnorm : ‖z‖ ≤ R + 2 := by
    calc
      ‖z‖ = ‖(z - 2) + 2‖ := by
        congr 1
        ring
      _ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = R + 2 := by
        rw [hnormsub]
        norm_num
  have hnorm1 : ‖z‖ + 1 ≤ R + 3 := by linarith
  have hnorm2 : ‖z‖ + 2 ≤ R + 4 := by linarith
  have hrpow : (‖z‖ + 2) ^ (3 / 2 : ℝ) ≤
      (R + 4) ^ (3 / 2 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hnorm2 (by norm_num)
  have hexp : Real.exp (k * (‖z‖ + 2) ^ (3 / 2 : ℝ)) ≤
      Real.exp (k * (R + 4) ^ (3 / 2 : ℝ)) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrpow hk.le)
  calc
    ‖riemannXi z‖ ≤
        (‖z‖ * (‖z‖ + 1) * K *
          Real.exp (k * (‖z‖ + 2) ^ (3 / 2 : ℝ)) + 1) / 2 := hxi z
    _ ≤ ((R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) ^ (3 / 2 : ℝ)) + 1) / 2 := by
      gcongr
    _ ≤ (R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) ^ (3 / 2 : ℝ)) + 1 := by
      have hnonneg : 0 ≤ (R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) ^ (3 / 2 : ℝ)) := by positivity
      linarith

/-- Pure order-`3 / 2` exponential sphere growth for Jensen's inequality. -/
theorem exists_riemannXi_sphere_exp_rpowThreeHalves_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ z ∈ Metric.sphere (2 : ℂ) R,
        ‖riemannXi z‖ ≤
          Real.exp (A * (R + 4) ^ (3 / 2 : ℝ)) := by
  obtain ⟨K, k, hK, hk, hbound⟩ :=
    exists_riemannXi_sphere_rpowThreeHalvesExp_bound
  let A : ℝ := K + k + 3
  refine ⟨A, by dsimp [A]; positivity, fun R hR z hz ↦ ?_⟩
  let u : ℝ := (R + 4) ^ (3 / 2 : ℝ)
  have hbase : 1 ≤ R + 4 := by linarith
  have hu1 : 1 ≤ u := by
    dsimp [u]
    exact Real.one_le_rpow hbase (by norm_num)
  have hlinear : R + 4 ≤ u := by
    dsimp [u]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (1 : ℝ) ≤ 3 / 2))
  have hR2 : R + 2 ≤ Real.exp u := by
    calc
      R + 2 ≤ u := by linarith
      _ ≤ Real.exp u :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp u)
  have hR3 : R + 3 ≤ Real.exp u := by
    calc
      R + 3 ≤ u := by linarith
      _ ≤ Real.exp u :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp u)
  have hKexp : K ≤ Real.exp (K * u) := by
    calc
      K ≤ K * u := by nlinarith
      _ ≤ Real.exp (K * u) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hpoly : (R + 2) * (R + 3) * K * Real.exp (k * u) ≤
      Real.exp ((K + k + 2) * u) := by
    calc
      (R + 2) * (R + 3) * K * Real.exp (k * u) ≤
          Real.exp u * Real.exp u * Real.exp (K * u) * Real.exp (k * u) := by
        gcongr
      _ = Real.exp ((K + k + 2) * u) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have htwo : (2 : ℝ) ≤ Real.exp u := by
    calc
      (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        norm_num at h ⊢
        exact h
      _ ≤ Real.exp u := Real.exp_le_exp.mpr hu1
  calc
    ‖riemannXi z‖ ≤ (R + 2) * (R + 3) * K *
        Real.exp (k * (R + 4) ^ (3 / 2 : ℝ)) + 1 := hbound R hR z hz
    _ ≤ Real.exp ((K + k + 2) * u) + 1 := by
      dsimp [u] at hpoly ⊢
      linarith
    _ ≤ 2 * Real.exp ((K + k + 2) * u) := by
      have hE : 1 ≤ Real.exp ((K + k + 2) * u) := by
        exact Real.one_le_exp (by positivity)
      linarith
    _ ≤ Real.exp u * Real.exp ((K + k + 2) * u) := by
      gcongr
    _ = Real.exp (A * (R + 4) ^ (3 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      dsimp [A, u]
      congr 1
      ring

/-- A global quadratic-exponential bound for Mathlib's entire
pole-subtracted completed zeta. This is the finite-order source estimate
needed by the xi/Jensen lane. -/
theorem exists_completedRiemannZeta₀_quadraticExp_bound :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤
        C * Real.exp (2 * (‖s‖ + 2) ^ 2 / p) *
          Real.exp (-(p / 2)) / (p / 2) := by
  obtain ⟨p, C, hp, hC, hkernel⟩ :=
    exists_riemannThetaKernel_global_exp_bound
  refine ⟨p, C, hp, hC, fun s ↦ ?_⟩
  let a : ℝ := ‖s‖ + 2
  let B : ℝ := C * Real.exp (2 * a ^ 2 / p)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hC0 : 0 ≤ C := hC.le
  have hw₁ : (s / 2 - 1).re ≤ a := by
    dsimp [a]
    norm_num
    nlinarith [Complex.re_le_norm s, norm_nonneg s]
  have hw₂ : ((1 - s) / 2 - 1).re ≤ a := by
    have hre : -s.re ≤ ‖s‖ := by
      have habs := Complex.abs_re_le_norm s
      exact (neg_le_abs s.re).trans habs
    dsimp [a]
    norm_num
    nlinarith
  have hdom : IntegrableOn
      (fun x : ℝ ↦ 2 * B * Real.exp (-(p / 2) * x)) (Ioi 1) := by
    exact (integrableOn_exp_mul_Ioi (by linarith : -(p / 2) < 0) 1).const_mul _
  have hnorm :
      ‖∫ x : ℝ in Ioi 1,
          ((x : ℂ) ^ (s / 2 - 1) +
            (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x‖ ≤
        ∫ x : ℝ in Ioi 1, 2 * B * Real.exp (-(p / 2) * x) := by
    apply norm_integral_le_of_norm_le hdom
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := hx.le
    have h₁ := norm_cpow_mul_riemannThetaKernel_le
      ha hp hC0 hx1 hw₁ (hkernel x hx1)
    have h₂ := norm_cpow_mul_riemannThetaKernel_le
      ha hp hC0 hx1 hw₂ (hkernel x hx1)
    calc
      ‖((x : ℂ) ^ (s / 2 - 1) +
          (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x‖ =
          ‖(x : ℂ) ^ (s / 2 - 1) * riemannThetaKernel x +
            (x : ℂ) ^ ((1 - s) / 2 - 1) * riemannThetaKernel x‖ := by
              congr 1
              ring
      _ ≤ ‖(x : ℂ) ^ (s / 2 - 1) * riemannThetaKernel x‖ +
          ‖(x : ℂ) ^ ((1 - s) / 2 - 1) * riemannThetaKernel x‖ := norm_add_le _ _
      _ ≤ B * Real.exp (-(p / 2) * x) + B * Real.exp (-(p / 2) * x) := by
        simpa only [B, mul_assoc] using add_le_add h₁ h₂
      _ = 2 * B * Real.exp (-(p / 2) * x) := by ring
  rw [completedRiemannZeta₀_eq_integral_Ioi, norm_div]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  calc
    ‖∫ x : ℝ in Ioi 1,
        ((x : ℂ) ^ (s / 2 - 1) +
          (x : ℂ) ^ ((1 - s) / 2 - 1)) * riemannThetaKernel x‖ / 2 ≤
        (∫ x : ℝ in Ioi 1, 2 * B * Real.exp (-(p / 2) * x)) / 2 := by
      gcongr
    _ = B * Real.exp (-(p / 2)) / (p / 2) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (by linarith : -(p / 2) < 0)]
      dsimp [B]
      field_simp
    _ = C * Real.exp (2 * (‖s‖ + 2) ^ 2 / p) *
        Real.exp (-(p / 2)) / (p / 2) := by rfl

/-- A conventional finite-order packaging of the preceding explicit bound. -/
theorem exists_completedRiemannZeta₀_finiteOrder_bound :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤
        K * Real.exp (k * (‖s‖ + 2) ^ 2) := by
  obtain ⟨p, C, hp, hC, hbound⟩ :=
    exists_completedRiemannZeta₀_quadraticExp_bound
  let K := C * Real.exp (-(p / 2)) / (p / 2)
  let k := 2 / p
  refine ⟨K, k, ?_, ?_, fun s ↦ ?_⟩
  · dsimp [K]
    positivity
  · dsimp [k]
    positivity
  · refine (hbound s).trans_eq ?_
    dsimp [K, k]
    ring_nf

/-- The xi normalization inherits an explicit quadratic-exponential global
bound, with only its defining quadratic polynomial left visible. -/
theorem exists_riemannXi_polynomial_quadraticExp_bound :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ s : ℂ,
      ‖riemannXi s‖ ≤
        (‖s‖ * (‖s‖ + 1) * K *
          Real.exp (k * (‖s‖ + 2) ^ 2) + 1) / 2 := by
  obtain ⟨K, k, hK, hk, hbound⟩ :=
    exists_completedRiemannZeta₀_finiteOrder_bound
  refine ⟨K, k, hK, hk, fun s ↦ ?_⟩
  have hsub : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    simpa using norm_sub_le s (1 : ℂ)
  unfold riemannXi
  rw [norm_div]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  calc
    ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ / 2 ≤
        (‖s * (s - 1) * completedRiemannZeta₀ s‖ + 1) / 2 := by
      gcongr
      simpa using norm_add_le (s * (s - 1) * completedRiemannZeta₀ s) (1 : ℂ)
    _ = (‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1) / 2 := by
      rw [norm_mul, norm_mul]
    _ ≤ (‖s‖ * (‖s‖ + 1) *
          (K * Real.exp (k * (‖s‖ + 2) ^ 2)) + 1) / 2 := by
      gcongr
      exact hbound s
    _ = (‖s‖ * (‖s‖ + 1) * K *
          Real.exp (k * (‖s‖ + 2) ^ 2) + 1) / 2 := by ring

/-- Literature-shaped finite-order growth on spheres centered at the
nonvanishing Jensen base point `2`. The displayed majorant is at least `1`,
so it can be passed directly to `AnalyticOnNhd.sum_divisor_le`. -/
theorem exists_riemannXi_sphere_quadraticExp_bound :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ z ∈ Metric.sphere (2 : ℂ) R,
        ‖riemannXi z‖ ≤
          (R + 2) * (R + 3) * K * Real.exp (k * (R + 4) ^ 2) + 1 := by
  obtain ⟨K, k, hK, hk, hxi⟩ :=
    exists_riemannXi_polynomial_quadraticExp_bound
  refine ⟨K, k, hK, hk, fun R hR z hz ↦ ?_⟩
  have hdist : dist z (2 : ℂ) = R := Metric.mem_sphere.mp hz
  have hnormsub : ‖z - 2‖ = R := by
    simpa only [dist_eq_norm] using hdist
  have hnorm : ‖z‖ ≤ R + 2 := by
    calc
      ‖z‖ = ‖(z - 2) + 2‖ := by
        congr 1
        ring
      _ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = R + 2 := by
        rw [hnormsub]
        norm_num
  have hnorm1 : ‖z‖ + 1 ≤ R + 3 := by linarith
  have hnorm2 : ‖z‖ + 2 ≤ R + 4 := by linarith
  have hsquares : (‖z‖ + 2) ^ 2 ≤ (R + 4) ^ 2 := by
    nlinarith [norm_nonneg z]
  have hexp : Real.exp (k * (‖z‖ + 2) ^ 2) ≤
      Real.exp (k * (R + 4) ^ 2) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsquares hk.le)
  calc
    ‖riemannXi z‖ ≤
        (‖z‖ * (‖z‖ + 1) * K *
          Real.exp (k * (‖z‖ + 2) ^ 2) + 1) / 2 := hxi z
    _ ≤ ((R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) ^ 2) + 1) / 2 := by
      gcongr
    _ ≤ (R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) ^ 2) + 1 := by
      have hnonneg : 0 ≤ (R + 2) * (R + 3) * K *
          Real.exp (k * (R + 4) ^ 2) := by positivity
      linarith

/-- Pure quadratic-exponential sphere growth, convenient for taking the
logarithm in Jensen's inequality. -/
theorem exists_riemannXi_sphere_exp_bound :
    ∃ A : Real, 0 < A ∧ ∀ R : Real, 0 ≤ R →
      ∀ z ∈ Metric.sphere (2 : Complex) R,
        ‖riemannXi z‖ ≤ Real.exp (A * (R + 4) ^ 2) := by
  obtain ⟨K, k, hK, hk, hbound⟩ :=
    exists_riemannXi_sphere_quadraticExp_bound
  let A : Real := K + k + 3
  refine ⟨A, by dsimp [A]; positivity, fun R hR z hz ↦ ?_⟩
  let u : Real := (R + 4) ^ 2
  have hu1 : 1 ≤ u := by
    dsimp [u]
    nlinarith [sq_nonneg (R + 4)]
  have hR2 : R + 2 ≤ Real.exp u := by
    calc
      R + 2 ≤ u := by dsimp [u]; nlinarith
      _ ≤ Real.exp u :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp u)
  have hR3 : R + 3 ≤ Real.exp u := by
    calc
      R + 3 ≤ u := by dsimp [u]; nlinarith
      _ ≤ Real.exp u :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp u)
  have hKexp : K ≤ Real.exp (K * u) := by
    calc
      K ≤ K * u := by nlinarith
      _ ≤ Real.exp (K * u) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hpoly : (R + 2) * (R + 3) * K * Real.exp (k * u) ≤
      Real.exp ((K + k + 2) * u) := by
    calc
      (R + 2) * (R + 3) * K * Real.exp (k * u) ≤
          Real.exp u * Real.exp u * Real.exp (K * u) * Real.exp (k * u) := by
        gcongr
      _ = Real.exp ((K + k + 2) * u) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have htwo : (2 : Real) ≤ Real.exp u := by
    calc
      (2 : Real) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : Real)
        norm_num at h ⊢
        exact h
      _ ≤ Real.exp u := Real.exp_le_exp.mpr hu1
  calc
    ‖riemannXi z‖ ≤ (R + 2) * (R + 3) * K *
        Real.exp (k * (R + 4) ^ 2) + 1 := hbound R hR z hz
    _ ≤ Real.exp ((K + k + 2) * u) + 1 := by
      dsimp [u] at hpoly ⊢
      linarith
    _ ≤ 2 * Real.exp ((K + k + 2) * u) := by
      have hE : 1 ≤ Real.exp ((K + k + 2) * u) := by
        exact Real.one_le_exp (by positivity)
      linarith
    _ ≤ Real.exp u * Real.exp ((K + k + 2) * u) := by
      gcongr
    _ = Real.exp (A * (R + 4) ^ 2) := by
      rw [← Real.exp_add]
      dsimp [A, u]
      congr 1
      ring

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
