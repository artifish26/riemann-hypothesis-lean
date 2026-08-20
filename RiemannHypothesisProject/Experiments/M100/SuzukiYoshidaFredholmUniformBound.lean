import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmForcing

/-!
# M100-DF6F uniform Fredholm forcing bounds

This module freezes the `L²` and source-dual bounds for Suzuki's two
projected Fredholm right-hand sides uniformly over the checked DF6E radius
window.  The majorant is the elementary endpoint value obtained by comparing
the truncated real exponentials with the normalized zero Fourier mode.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

/-- Elementary `L²` majorant for a truncated real exponential on `[-a,a]`. -/
theorem norm_suzukiFredholmExponentialL2_le
    {a : Real} (ha : 0 < a) (c : Real) :
    ‖suzukiFredholmExponentialL2 ha c‖ ≤
      Real.exp (|c| * a) * Real.sqrt (2 * a) := by
  have hbound : ‖suzukiFredholmExponentialL2 ha c‖ ≤
      (Real.exp (|c| * a) * Real.sqrt (2 * a)) *
        ‖suzukiYoshidaExponentialL2 a ha 0‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
      (c := Real.exp (|c| * a) * Real.sqrt (2 * a))
      (f := suzukiFredholmExponentialL2 ha c)
      (g := suzukiYoshidaExponentialL2 a ha 0)
    filter_upwards [
      suzukiFredholmExponentialL2_coeFn ha c,
      suzukiYoshidaExponentialL2_coeFn ha 0] with x hfredholm hzero
    rw [hfredholm, hzero]
    by_cases hx : x ∈ Set.Icc (-a) a
    · rw [suzukiFredholmExponentialFunction,
        suzukiYoshidaExponentialFunction,
        Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have hsqrt : 0 < Real.sqrt (2 * a) := by positivity
      have hexp : Real.exp (c * x) ≤ Real.exp (|c| * a) := by
        apply Real.exp_le_exp.mpr
        calc
          c * x ≤ |c * x| := le_abs_self _
          _ = |c| * |x| := abs_mul c x
          _ ≤ |c| * a := by
            exact mul_le_mul_of_nonneg_left ((abs_le).2 hx) (abs_nonneg c)
      have hfredholmNorm :
          ‖(Real.exp (c * x) : Complex)‖ = Real.exp (c * x) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      have hzeroNorm :
          ‖(((Real.sqrt (2 * a))⁻¹ : Complex) *
              Complex.exp
                (Complex.I *
                  (((0 : Int) : Complex) * (Real.pi : Complex) /
                    (a : Complex)) * (x : Complex)))‖ =
            (Real.sqrt (2 * a))⁻¹ := by
        have hsqrtA : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
        have hsqrtTwo : 0 < Real.sqrt 2 := by positivity
        simp [Real.norm_eq_abs, abs_of_pos hsqrtA,
          abs_of_pos hsqrtTwo]
      rw [hfredholmNorm, hzeroNorm, mul_assoc,
        mul_inv_cancel₀ hsqrt.ne', mul_one]
      exact hexp
    · simp [suzukiFredholmExponentialFunction,
        suzukiYoshidaExponentialFunction, hx]
  simpa [(orthonormal_suzukiYoshidaExponentialL2 ha).norm_eq_one]
    using hbound

/-- Radius-independent forcing constant on the checked DF6E window. -/
def suzukiDF6FUniformFredholmBound : Real :=
  Real.exp suzukiProjectAStar *
    Real.sqrt (2 * suzukiProjectAStar)

theorem suzukiDF6FUniformFredholmBound_pos :
    0 < suzukiDF6FUniformFredholmBound := by
  unfold suzukiDF6FUniformFredholmBound
  exact mul_pos (Real.exp_pos _)
    (Real.sqrt_pos.2 (mul_pos (by norm_num) suzukiProjectAStar_pos))

/-- A coarse rational enclosure of the frozen endpoint constant.  The margin
is intentionally generous: `A* < log 2 < 1`, `exp 1 < 3`, and
`sqrt 2 < 3/2`. -/
theorem suzukiDF6FUniformFredholmBound_lt_five :
    suzukiDF6FUniformFredholmBound < 5 := by
  have hlogTwo : Real.log 2 < 1 := by
    rw [← Real.exp_lt_exp]
    rw [Real.exp_log (by norm_num)]
    exact Real.exp_one_gt_two
  have hAStar : suzukiProjectAStar < 1 :=
    suzukiProjectAStar_lt_log_two.trans hlogTwo
  have hexp : Real.exp suzukiProjectAStar < 3 :=
    (Real.exp_lt_exp.mpr hAStar).trans Real.exp_one_lt_three
  have hsqrt : Real.sqrt (2 * suzukiProjectAStar) < 3 / 2 := by
    calc
      Real.sqrt (2 * suzukiProjectAStar) < Real.sqrt 2 := by
        apply Real.sqrt_lt_sqrt
          (mul_pos (by norm_num) suzukiProjectAStar_pos).le
        nlinarith
      _ < 3 / 2 := Real.sqrt_two_lt_three_halves
  unfold suzukiDF6FUniformFredholmBound
  calc
    Real.exp suzukiProjectAStar * Real.sqrt (2 * suzukiProjectAStar) <
        3 * Real.sqrt (2 * suzukiProjectAStar) :=
      mul_lt_mul_of_pos_right hexp
        (Real.sqrt_pos.2 (mul_pos (by norm_num) suzukiProjectAStar_pos))
    _ < 3 * (3 / 2 : Real) := mul_lt_mul_of_pos_left hsqrt (by norm_num)
    _ < 5 := by norm_num

/-- Both signs of the Fredholm exponential have the same endpoint-uniform
`L²` majorant. -/
theorem norm_suzukiFredholmExponentialL2_one_le_uniform
    {a : Real} (ha : a ∈ SuzukiDF6EInterval) (c : Real)
    (hc : |c| = 1) :
    ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c‖ ≤
      suzukiDF6FUniformFredholmBound := by
  have hlocal := norm_suzukiFredholmExponentialL2_le
    (suzukiDF6E_radius_pos ha) c
  rw [hc, one_mul] at hlocal
  apply hlocal.trans
  unfold suzukiDF6FUniformFredholmBound
  have hexp : Real.exp a ≤ Real.exp suzukiProjectAStar :=
    Real.exp_le_exp.mpr ha.2
  have hsqrt : Real.sqrt (2 * a) ≤
      Real.sqrt (2 * suzukiProjectAStar) := by
    apply Real.sqrt_le_sqrt
    linarith [ha.2]
  exact mul_le_mul hexp hsqrt (Real.sqrt_nonneg _) (Real.exp_pos _).le

/-- Fully numerical `L²` bound for both Fredholm exponential signs on the
checked window. -/
theorem norm_suzukiFredholmExponentialL2_one_lt_five
    {a : Real} (ha : a ∈ SuzukiDF6EInterval) (c : Real)
    (hc : |c| = 1) :
    ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c‖ < 5 :=
  (norm_suzukiFredholmExponentialL2_one_le_uniform ha c hc).trans_lt
    suzukiDF6FUniformFredholmBound_lt_five

/-- Uniform source-dual bound for Suzuki's projected plus forcing. -/
theorem suzukiSourceKDualBoundAt_fredholmPlus_uniform
    {a : Real} (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiSourceKDualBoundAt a (suzukiFredholmPlusForcing a)
      suzukiDF6FUniformFredholmBound := by
  intro u
  exact (suzukiSourceKDualBoundAt_fredholmPlus
      (suzukiDF6E_radius_pos ha) u).trans
    (mul_le_mul_of_nonneg_right
      (norm_suzukiFredholmExponentialL2_one_le_uniform ha 1 (by simp))
      (suzukiSourceKSeminorm_nonneg a u))

/-- Uniform source-dual bound for Suzuki's projected minus forcing. -/
theorem suzukiSourceKDualBoundAt_fredholmMinus_uniform
    {a : Real} (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiSourceKDualBoundAt a (suzukiFredholmMinusForcing a)
      suzukiDF6FUniformFredholmBound := by
  intro u
  exact (suzukiSourceKDualBoundAt_fredholmMinus
      (suzukiDF6E_radius_pos ha) u).trans
    (mul_le_mul_of_nonneg_right
      (norm_suzukiFredholmExponentialL2_one_le_uniform ha (-1) (by simp))
      (suzukiSourceKSeminorm_nonneg a u))

/-- Rational source-dual bound for the projected plus forcing. -/
theorem suzukiSourceKDualBoundAt_fredholmPlus_five
    {a : Real} (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiSourceKDualBoundAt a (suzukiFredholmPlusForcing a) 5 := by
  intro u
  exact (suzukiSourceKDualBoundAt_fredholmPlus_uniform ha u).trans
    (mul_le_mul_of_nonneg_right
      suzukiDF6FUniformFredholmBound_lt_five.le
      (suzukiSourceKSeminorm_nonneg a u))

/-- Rational source-dual bound for the projected minus forcing. -/
theorem suzukiSourceKDualBoundAt_fredholmMinus_five
    {a : Real} (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiSourceKDualBoundAt a (suzukiFredholmMinusForcing a) 5 := by
  intro u
  exact (suzukiSourceKDualBoundAt_fredholmMinus_uniform ha u).trans
    (mul_le_mul_of_nonneg_right
      suzukiDF6FUniformFredholmBound_lt_five.le
      (suzukiSourceKSeminorm_nonneg a u))

/-- Uniform DF6F source-seminorm estimate for a shifted plus-forcing
solution on the checked radius window. -/
theorem suzukiDF6F_fredholmPlus_solution_sourceKSeminorm_le_uniform
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmPlusForcing a) :
    suzukiSourceKSeminorm a u ≤
      suzukiDF6FUniformFredholmBound /
        ((1 / 400000 : Real) - lambda) := by
  exact suzukiDF6F_sourceKSeminorm_solution_le
    hsource hequation25 ha hlambda
    suzukiDF6FUniformFredholmBound_pos.le
    (suzukiSourceKDualBoundAt_fredholmPlus_uniform ha) hsolve

/-- Uniform DF6F source-seminorm estimate for a shifted minus-forcing
solution on the checked radius window. -/
theorem suzukiDF6F_fredholmMinus_solution_sourceKSeminorm_le_uniform
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmMinusForcing a) :
    suzukiSourceKSeminorm a u ≤
      suzukiDF6FUniformFredholmBound /
        ((1 / 400000 : Real) - lambda) := by
  exact suzukiDF6F_sourceKSeminorm_solution_le
    hsource hequation25 ha hlambda
    suzukiDF6FUniformFredholmBound_pos.le
    (suzukiSourceKDualBoundAt_fredholmMinus_uniform ha) hsolve

/-- Uniform zero-shift plus-forcing estimate on the checked radius window. -/
theorem suzukiDF6F_sourceG_fredholmPlus_solution_sourceKSeminorm_le_uniform
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceGOperator a u = suzukiFredholmPlusForcing a) :
    suzukiSourceKSeminorm a u ≤
      400000 * suzukiDF6FUniformFredholmBound := by
  exact suzukiDF6F_sourceG_solution_sourceKSeminorm_le
    hsource hequation25 ha suzukiDF6FUniformFredholmBound_pos.le
    (suzukiSourceKDualBoundAt_fredholmPlus_uniform ha) hsolve

/-- Uniform zero-shift minus-forcing estimate on the checked radius window. -/
theorem suzukiDF6F_sourceG_fredholmMinus_solution_sourceKSeminorm_le_uniform
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceGOperator a u = suzukiFredholmMinusForcing a) :
    suzukiSourceKSeminorm a u ≤
      400000 * suzukiDF6FUniformFredholmBound := by
  exact suzukiDF6F_sourceG_solution_sourceKSeminorm_le
    hsource hequation25 ha suzukiDF6FUniformFredholmBound_pos.le
    (suzukiSourceKDualBoundAt_fredholmMinus_uniform ha) hsolve

/-- Fully numerical shifted plus-forcing estimate. -/
theorem suzukiDF6F_fredholmPlus_solution_sourceKSeminorm_le_five
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmPlusForcing a) :
    suzukiSourceKSeminorm a u ≤
      5 / ((1 / 400000 : Real) - lambda) := by
  exact suzukiDF6F_sourceKSeminorm_solution_le
    hsource hequation25 ha hlambda (by norm_num)
    (suzukiSourceKDualBoundAt_fredholmPlus_five ha) hsolve

/-- Fully numerical shifted minus-forcing estimate. -/
theorem suzukiDF6F_fredholmMinus_solution_sourceKSeminorm_le_five
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmMinusForcing a) :
    suzukiSourceKSeminorm a u ≤
      5 / ((1 / 400000 : Real) - lambda) := by
  exact suzukiDF6F_sourceKSeminorm_solution_le
    hsource hequation25 ha hlambda (by norm_num)
    (suzukiSourceKDualBoundAt_fredholmMinus_five ha) hsolve

/-- Fully numerical zero-shift plus-forcing estimate. -/
theorem suzukiDF6F_sourceG_fredholmPlus_solution_sourceKSeminorm_le_twoMillion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceGOperator a u = suzukiFredholmPlusForcing a) :
    suzukiSourceKSeminorm a u ≤ 2000000 := by
  convert suzukiDF6F_sourceG_solution_sourceKSeminorm_le
    hsource hequation25 ha (C := 5) (by norm_num)
    (suzukiSourceKDualBoundAt_fredholmPlus_five ha) hsolve using 1;
    norm_num

/-- Fully numerical zero-shift minus-forcing estimate. -/
theorem suzukiDF6F_sourceG_fredholmMinus_solution_sourceKSeminorm_le_twoMillion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceGOperator a u = suzukiFredholmMinusForcing a) :
    suzukiSourceKSeminorm a u ≤ 2000000 := by
  convert suzukiDF6F_sourceG_solution_sourceKSeminorm_le
    hsource hequation25 ha (C := 5) (by norm_num)
    (suzukiSourceKDualBoundAt_fredholmMinus_five ha) hsolve using 1;
    norm_num

end

end RiemannHypothesisProject.Experiments.M100
