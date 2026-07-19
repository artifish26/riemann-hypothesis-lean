import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Local logarithmic-derivative bounds

This module isolates the Borel-Caratheodory and Cauchy-estimate step in the
good-height argument.  Its input is the normalized analytic logarithm of a
zero-free factor; construction of that factor belongs to the source-theorem
layer above this file.
-/

namespace RiemannHypothesisProject

open Complex Metric Set

noncomputable section

/-- A zero-free analytic function on a disk has a normalized analytic
logarithm.  The final identity is the quantitative form used by
Borel-Caratheodory. -/
theorem exists_normalized_log_of_analyticOnNhd_ball
    {g : Complex -> Complex} {R : Real} (hR : 0 < R)
    (hg : AnalyticOnNhd Complex g (ball 0 R))
    (hg_ne : ∀ z ∈ ball (0 : Complex) R, g z ≠ 0) :
    ∃ L : Complex -> Complex,
      L 0 = 0 ∧
      (∀ z ∈ ball (0 : Complex) R,
        HasDerivAt L (logDeriv g z) z) ∧
      ∀ z ∈ ball (0 : Complex) R,
        Real.exp (L z).re = norm (g z) / norm (g 0) := by
  have hg_diff : DifferentiableOn Complex g (ball (0 : Complex) R) :=
    hg.differentiableOn
  have hderiv_diff :
      DifferentiableOn Complex (deriv g) (ball (0 : Complex) R) :=
    hg.deriv.differentiableOn
  have hlogDeriv_diff :
      DifferentiableOn Complex (logDeriv g) (ball (0 : Complex) R) := by
    intro z hz
    change DifferentiableWithinAt Complex (deriv g / g) (ball 0 R) z
    exact (hderiv_diff z hz).div (hg_diff z hz) (hg_ne z hz)
  obtain ⟨L, hL_zero, hL⟩ :=
    hlogDeriv_diff.isExactOn_ball.with_val_at (0 : Complex) 0
  refine ⟨L, hL_zero, hL, fun z hz => ?_⟩
  let F : Complex -> Complex := fun w => Complex.exp (-L w) * g w
  have hF_deriv : ∀ w ∈ ball (0 : Complex) R, HasDerivAt F 0 w := by
    intro w hw
    have hLw := hL w hw
    have hgw := (hg w hw).differentiableAt.hasDerivAt
    have hproduct := hLw.neg.cexp.mul hgw
    refine (hproduct.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [logDeriv_apply]
      field_simp [hg_ne w hw]
      ring_nf
    · filter_upwards with v
      dsimp only [F]
      simp only [Pi.mul_apply, Pi.neg_apply]
  have hF_diff : DifferentiableOn Complex F (ball (0 : Complex) R) :=
    fun w hw => (hF_deriv w hw).differentiableAt.differentiableWithinAt
  have hF_const : F z = F 0 := by
    apply isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball (0 : Complex) R).isPreconnected hF_diff
      (fun w hw => (hF_deriv w hw).deriv) hz
    exact mem_ball_self hR
  have hg_zero_ne : g 0 ≠ 0 := hg_ne 0 (mem_ball_self hR)
  have hnorm : norm (g z) = norm (g 0) * Real.exp (L z).re := by
    have hnorm_const := congrArg norm hF_const
    simp only [F, hL_zero, neg_zero, Complex.exp_zero, one_mul,
      norm_mul, Complex.norm_exp, neg_re] at hnorm_const
    have hexp_ne : Real.exp (-(L z).re) ≠ 0 := (Real.exp_pos _).ne'
    calc
      norm (g z) =
          (Real.exp (-(L z).re) * norm (g z)) /
            Real.exp (-(L z).re) := by field_simp
      _ = norm (g 0) / Real.exp (-(L z).re) := by rw [hnorm_const]
      _ = norm (g 0) * Real.exp (L z).re := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 1
        ring_nf
  rw [hnorm]
  field_simp [norm_ne_zero_iff.mpr hg_zero_ne]

/-- A quantitative local derivative estimate for a normalized analytic
logarithm.  The deliberately loose constant keeps later radius arithmetic
elementary. -/
theorem norm_deriv_le_of_re_le_on_ball
    {L : Complex -> Complex} {R r M : Real}
    (hR : 0 < R) (hrR : r < R)
    (hL : DifferentiableOn Complex L (ball 0 R))
    (hL_zero : L 0 = 0)
    (hL_re : MapsTo L (ball 0 R) {z | z.re <= M})
    (hM : 0 < M) {z : Complex} (hz : z ∈ closedBall 0 r) :
    norm (deriv L z) <= 8 * M * R / (R - r) ^ 2 := by
  let d : Real := (R - r) / 2
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hz_norm : norm z <= r := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hclosed : closedBall z d ⊆ ball (0 : Complex) R := by
    intro w hw
    have hwz : norm (w - z) <= d := by
      simpa [mem_closedBall, dist_eq_norm] using hw
    have hw_norm : norm w <= r + d := by
      calc
        norm w = norm ((w - z) + z) := by ring_nf
        _ <= norm (w - z) + norm z := norm_add_le _ _
        _ <= r + d := by linarith
    have hrd : r + d < R := by
      dsimp [d]
      linarith
    simpa [mem_ball, dist_zero_right] using hw_norm.trans_lt hrd
  have hdiff : DiffContOnCl Complex L (ball z d) :=
    hL.diffContOnCl_ball hclosed
  have hsphere : ∀ w ∈ sphere z d,
      norm (L w) <= 4 * M * R / (R - r) := by
    intro w hw
    have hw_closed : w ∈ closedBall z d := sphere_subset_closedBall hw
    have hw_ball : w ∈ ball (0 : Complex) R := hclosed hw_closed
    have hw_norm_lt : norm w < R := by
      simpa [mem_ball, dist_zero_right] using hw_ball
    have hw_norm_nonneg : 0 <= norm w := norm_nonneg _
    have hdenom : 0 < R - norm w := sub_pos.mpr hw_norm_lt
    have hlocal :=
      borelCaratheodory_zero hM hL hL_re hR hw_ball hL_zero
    have hwz : norm (w - z) = d := by
      simpa [mem_sphere, dist_eq_norm] using hw
    have hw_norm_le : norm w <= r + d := by
      calc
        norm w = norm ((w - z) + z) := by ring_nf
        _ <= norm (w - z) + norm z := norm_add_le _ _
        _ = d + norm z := by rw [hwz]
        _ <= d + r := by linarith
        _ = r + d := add_comm d r
    have hdenom_lower : (R - r) / 2 <= R - norm w := by
      dsimp [d] at hw_norm_le
      linarith
    calc
      norm (L w) <= 2 * M * norm w / (R - norm w) := hlocal
      _ <= 2 * M * R / ((R - r) / 2) := by
        gcongr
      _ = 4 * M * R / (R - r) := by
        (field_simp; norm_num)
  have hcauchy :=
    norm_deriv_le_of_forall_mem_sphere_norm_le hd hdiff hsphere
  calc
    norm (deriv L z) <= (4 * M * R / (R - r)) / d := hcauchy
    _ = 8 * M * R / (R - r) ^ 2 := by
      dsimp [d]
      (field_simp; norm_num)

/-- A zero-free analytic factor whose norm is controlled relative to its
center has a quantitative logarithmic-derivative bound on every smaller
closed disk. -/
theorem norm_logDeriv_le_of_norm_le_mul_center_on_ball
    {g : Complex -> Complex} {R r B : Real}
    (hR : 0 < R) (hrR : r < R) (hB : 1 < B)
    (hg : AnalyticOnNhd Complex g (ball 0 R))
    (hg_ne : ∀ z ∈ ball (0 : Complex) R, g z ≠ 0)
    (hbound : ∀ z ∈ ball (0 : Complex) R,
      norm (g z) <= B * norm (g 0))
    {z : Complex} (hz : z ∈ closedBall 0 r) :
    norm (logDeriv g z) <=
      8 * Real.log B * R / (R - r) ^ 2 := by
  obtain ⟨L, hL_zero, hL_deriv, hL_norm⟩ :=
    exists_normalized_log_of_analyticOnNhd_ball hR hg hg_ne
  have hL_diff : DifferentiableOn Complex L (ball (0 : Complex) R) :=
    fun w hw => (hL_deriv w hw).differentiableAt.differentiableWithinAt
  have hg_zero_ne : g 0 ≠ 0 := hg_ne 0 (mem_ball_self hR)
  have hL_re : MapsTo L (ball (0 : Complex) R)
      {w | w.re <= Real.log B} := by
    intro w hw
    have hratio : norm (g w) / norm (g 0) <= B := by
      exact (div_le_iff₀ (norm_pos_iff.mpr hg_zero_ne)).mpr (hbound w hw)
    have hexp : Real.exp (L w).re <= Real.exp (Real.log B) := by
      rw [hL_norm w hw, Real.exp_log (zero_lt_one.trans hB)]
      exact hratio
    exact Real.exp_le_exp.mp hexp
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hlocal := norm_deriv_le_of_re_le_on_ball
    hR hrR hL_diff hL_zero hL_re hlogB hz
  have hz_ball : z ∈ ball (0 : Complex) R := by
    have hz_norm : norm z <= r := by
      simpa [mem_closedBall, dist_zero_right] using hz
    simpa [mem_ball, dist_zero_right] using hz_norm.trans_lt hrR
  rw [(hL_deriv z hz_ball).deriv] at hlocal
  exact hlocal

/-- The local logarithmic derivative equals the multiplicity-weighted
principal-part sum plus the logarithmic derivative of the zero-free factor.
The latter is bounded by the preceding Borel-Caratheodory theorem. -/
theorem norm_logDeriv_sub_principalPart_le_of_local_factorization
    {f g : Complex -> Complex} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat} {R r B : Real}
    (hR : 0 < R) (hrR : r < R) (hB : 1 < B)
    (hg : AnalyticOnNhd Complex g (ball 0 R))
    (hg_ne : ∀ w ∈ ball (0 : Complex) R, g w ≠ 0)
    (hbound : ∀ w ∈ ball (0 : Complex) R,
      norm (g w) <= B * norm (g 0))
    (hfactor : EqOn f
      (fun w =>
        (∏ u ∈ zeros, (w - u) ^ multiplicity u) * g w)
      (ball (0 : Complex) R))
    {z : Complex} (hz : z ∈ closedBall 0 r)
    (hz_ne : ∀ u ∈ zeros, z ≠ u) :
    norm
        (logDeriv f z -
          ∑ u ∈ zeros, (multiplicity u : Complex) / (z - u)) <=
      8 * Real.log B * R / (R - r) ^ 2 := by
  have hz_ball : z ∈ ball (0 : Complex) R := by
    have hz_norm : norm z <= r := by
      simpa [mem_closedBall, dist_zero_right] using hz
    simpa [mem_ball, dist_zero_right] using hz_norm.trans_lt hrR
  let P : Complex -> Complex := fun w =>
    ∏ u ∈ zeros, (w - u) ^ multiplicity u
  have hP_ne : P z ≠ 0 := by
    dsimp [P]
    simp only [Finset.prod_ne_zero_iff]
    exact fun u hu => pow_ne_zero _ (sub_ne_zero.mpr (hz_ne u hu))
  have hP_diff : DifferentiableAt Complex P z := by
    dsimp [P]
    fun_prop
  have hg_diff : DifferentiableAt Complex g z :=
    (hg z hz_ball).differentiableAt
  have hlog_factor : logDeriv f z = logDeriv (fun w => P w * g w) z := by
    simp only [logDeriv_apply]
    rw [hfactor.deriv isOpen_ball hz_ball, hfactor hz_ball]
  have hP_log :
      logDeriv P z =
        ∑ u ∈ zeros, (multiplicity u : Complex) / (z - u) := by
    dsimp [P]
    rw [logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [logDeriv_fun_pow (by fun_prop)]
      simp only [logDeriv_apply]
      rw [deriv_sub_const]
      simp [div_eq_mul_inv]
    · intro u hu
      exact pow_ne_zero _ (sub_ne_zero.mpr (hz_ne u hu))
    · intro u hu
      fun_prop
  rw [hlog_factor, logDeriv_mul z hP_ne (hg_ne z hz_ball) hP_diff hg_diff,
    hP_log, add_sub_cancel_left]
  exact norm_logDeriv_le_of_norm_le_mul_center_on_ball
    hR hrR hB hg hg_ne hbound hz

end

end RiemannHypothesisProject
