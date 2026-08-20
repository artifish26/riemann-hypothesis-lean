import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointSmoothWitnessPositivity

/-!
# Smooth-transform identity reduction for M100-DF6D4

This module isolates the exact elementary pole transform from the remaining
archimedean transform identity.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set

def suzukiDF6D4PolePrimitive (w t : Real) : Real :=
  ((1 / 2 : Real) * Real.sinh (t / 2) * Real.sin (w * t) -
      w * Real.cosh (t / 2) * Real.cos (w * t)) /
    (w ^ 2 + 1 / 4)

def suzukiDF6D4ArchimedeanPrimitive (d w t : Real) : Real :=
  Real.exp (-d * t) *
      (-d * Real.sin (w * t) - w * Real.cos (w * t)) /
    (d ^ 2 + w ^ 2)

private theorem hasDerivAt_sinh_half (t : Real) :
    HasDerivAt (fun x : Real => Real.sinh (x / 2))
      (Real.cosh (t / 2) / 2) t := by
  have h := (Real.hasDerivAt_sinh (t / 2)).comp t
    ((hasDerivAt_id t).div_const 2)
  have heq :
      (Real.sinh ∘ fun x : Real => id x / 2) =ᶠ[nhds t]
        fun x : Real => Real.sinh (x / 2) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

private theorem hasDerivAt_cosh_half (t : Real) :
    HasDerivAt (fun x : Real => Real.cosh (x / 2))
      (Real.sinh (t / 2) / 2) t := by
  have h := (Real.hasDerivAt_cosh (t / 2)).comp t
    ((hasDerivAt_id t).div_const 2)
  have heq :
      (Real.cosh ∘ fun x : Real => id x / 2) =ᶠ[nhds t]
        fun x : Real => Real.cosh (x / 2) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

private theorem hasDerivAt_sin_mul (w t : Real) :
    HasDerivAt (fun x : Real => Real.sin (w * x))
      (w * Real.cos (w * t)) t := by
  have h := (Real.hasDerivAt_sin (w * t)).comp t
    ((hasDerivAt_id t).const_mul w)
  have heq :
      (Real.sin ∘ fun x : Real => w * id x) =ᶠ[nhds t]
        fun x : Real => Real.sin (w * x) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

private theorem hasDerivAt_cos_mul (w t : Real) :
    HasDerivAt (fun x : Real => Real.cos (w * x))
      (-w * Real.sin (w * t)) t := by
  have h := (Real.hasDerivAt_cos (w * t)).comp t
    ((hasDerivAt_id t).const_mul w)
  have heq :
      (Real.cos ∘ fun x : Real => w * id x) =ᶠ[nhds t]
        fun x : Real => Real.cos (w * x) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

private theorem hasDerivAt_exp_neg_mul (d t : Real) :
    HasDerivAt (fun x : Real => Real.exp (-d * x))
      (-d * Real.exp (-d * t)) t := by
  have h := (Real.hasDerivAt_exp (-d * t)).comp t
    ((hasDerivAt_id t).const_mul (-d))
  have heq :
      (Real.exp ∘ fun x : Real => -d * id x) =ᶠ[nhds t]
        fun x : Real => Real.exp (-d * x) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

theorem hasDerivAt_suzukiDF6D4ArchimedeanPrimitive
    {d w t : Real} (hden : d ^ 2 + w ^ 2 ≠ 0) :
    HasDerivAt (suzukiDF6D4ArchimedeanPrimitive d w)
      (Real.exp (-d * t) * Real.sin (w * t)) t := by
  have hBracket :=
    (hasDerivAt_sin_mul w t).const_mul (-d) |>.add
      ((hasDerivAt_cos_mul w t).const_mul (-w))
  have h := ((hasDerivAt_exp_neg_mul d t).mul hBracket).div_const
    (d ^ 2 + w ^ 2)
  unfold suzukiDF6D4ArchimedeanPrimitive
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    simp only [Pi.mul_apply, Pi.add_apply]
    ring
  · field_simp [hden]
    simp only [Pi.add_apply]
    ring

theorem integral_exp_neg_mul_mul_sin_eq_archimedeanPrimitive_sub
    {d w L : Real} (hden : d ^ 2 + w ^ 2 ≠ 0) :
    (∫ t in (0 : Real)..L,
        Real.exp (-d * t) * Real.sin (w * t)) =
      suzukiDF6D4ArchimedeanPrimitive d w L -
        suzukiDF6D4ArchimedeanPrimitive d w 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    exact hasDerivAt_suzukiDF6D4ArchimedeanPrimitive hden
  · exact ContinuousOn.intervalIntegrable
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul
          (Real.continuous_sin.comp
            (continuous_const.mul continuous_id))).continuousOn

theorem hasDerivAt_suzukiDF6D4PolePrimitive
    {w t : Real} :
    HasDerivAt (suzukiDF6D4PolePrimitive w)
      (Real.cosh (t / 2) * Real.sin (w * t)) t := by
  have hNumerator :=
    (((hasDerivAt_sinh_half t).const_mul (1 / 2 : Real)).mul
      (hasDerivAt_sin_mul w t)).sub
        (((hasDerivAt_cosh_half t).const_mul w).mul
          (hasDerivAt_cos_mul w t))
  have h := hNumerator.div_const (w ^ 2 + 1 / 4)
  unfold suzukiDF6D4PolePrimitive
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    rfl
  · field_simp
    ring

theorem integral_cosh_half_mul_sin_eq_polePrimitive_sub
    (w L : Real) :
    (∫ t in (0 : Real)..L,
        Real.cosh (t / 2) * Real.sin (w * t)) =
      suzukiDF6D4PolePrimitive w L - suzukiDF6D4PolePrimitive w 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    exact hasDerivAt_suzukiDF6D4PolePrimitive
  · exact ContinuousOn.intervalIntegrable
      ((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul
        (Real.continuous_sin.comp
          (continuous_const.mul continuous_id))).continuousOn

theorem suzukiDF6D4PoleSineTransform_eq_kernel_integral (mode : Nat) :
    suzukiDF6D4PoleSineTransform mode =
      -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        -(Real.exp (t / 2) + Real.exp (-t / 2)) *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have harg : w * (2 * suzukiProjectAStar) =
      (mode : Real) * (2 * Real.pi) := by
    dsimp only [w]
    field_simp [suzukiProjectAStar_pos.ne']
  have hsin : Real.sin (w * (2 * suzukiProjectAStar)) = 0 := by
    rw [harg, ← sub_zero ((mode : Real) * (2 * Real.pi)),
      Real.sin_nat_mul_two_pi_sub]
    simp
  have hcos : Real.cos (w * (2 * suzukiProjectAStar)) = 1 := by
    rw [harg]
    exact Real.cos_nat_mul_two_pi mode
  have hintegral := integral_cosh_half_mul_sin_eq_polePrimitive_sub
    w (2 * suzukiProjectAStar)
  have hkernel :
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          -(Real.exp (t / 2) + Real.exp (-t / 2)) * Real.sin (w * t)) =
        -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          Real.cosh (t / 2) * Real.sin (w * t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    change -(Real.exp (t / 2) + Real.exp (-t / 2)) * Real.sin (w * t) =
      -2 * (Real.cosh (t / 2) * Real.sin (w * t))
    rw [Real.cosh_eq]
    ring
  unfold suzukiDF6D4PoleSineTransform
  dsimp only
  change 4 * w * (1 - Real.cosh suzukiProjectAStar) /
      (w ^ 2 + 1 / 4) = _
  rw [hkernel, hintegral]
  unfold suzukiDF6D4PolePrimitive
  rw [hsin, hcos]
  norm_num
  ring

theorem two_mul_integral_restorationKernel_eq_digammaSummand_sub
    (mode k : Nat) :
    2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      Real.exp (-suzukiDF6D4RestorationDecay k * t) *
        Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
      suzukiDF6D4DigammaSummand k
          ((mode : Real) * Real.pi / suzukiProjectAStar) -
        suzukiDF6D4RestorationTerm mode k := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  let d : Real := suzukiDF6D4RestorationDecay k
  have hd : 0 < d := by
    dsimp only [d]
    unfold suzukiDF6D4RestorationDecay
    positivity
  have hden : d ^ 2 + w ^ 2 ≠ 0 := by positivity
  have harg : w * (2 * suzukiProjectAStar) =
      (mode : Real) * (2 * Real.pi) := by
    dsimp only [w]
    field_simp [suzukiProjectAStar_pos.ne']
  have hsin : Real.sin (w * (2 * suzukiProjectAStar)) = 0 := by
    rw [harg, ← sub_zero ((mode : Real) * (2 * Real.pi)),
      Real.sin_nat_mul_two_pi_sub]
    simp
  have hcos : Real.cos (w * (2 * suzukiProjectAStar)) = 1 := by
    rw [harg]
    exact Real.cos_nat_mul_two_pi mode
  have hintegral :=
    integral_exp_neg_mul_mul_sin_eq_archimedeanPrimitive_sub
      (d := d) (w := w) (L := 2 * suzukiProjectAStar) hden
  change 2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      Real.exp (-d * t) * Real.sin (w * t)) = _
  rw [hintegral]
  unfold suzukiDF6D4ArchimedeanPrimitive
  rw [hsin, hcos]
  unfold suzukiDF6D4DigammaSummand suzukiDF6D4RestorationTerm
  dsimp only [w, d]
  unfold suzukiDF6D4RestorationDecay
  norm_num
  field_simp
  ring

theorem summable_two_mul_integral_restorationKernel (mode : Nat) :
    Summable (fun k : Nat =>
      2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-suzukiDF6D4RestorationDecay k * t) *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))) := by
  have hDigamma := summable_suzukiDF6D4DigammaSummand
    ((mode : Real) * Real.pi / suzukiProjectAStar)
  have hRestoration : Summable
      (fun k : Nat => suzukiDF6D4RestorationTerm mode k) := by
    simpa only [Nat.zero_add] using
      summable_suzukiDF6D4RestorationTail mode 0
  exact (hDigamma.sub hRestoration).congr fun k =>
    (two_mul_integral_restorationKernel_eq_digammaSummand_sub mode k).symm

theorem tsum_two_mul_integral_restorationKernel_eq_digamma_im_sub
    (mode : Nat) :
    (∑' k : Nat,
      2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-suzukiDF6D4RestorationDecay k * t) *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))) =
      (Complex.digamma
        ((1 / 4 : Complex) +
          (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
            Complex.I)).im -
        ∑' k : Nat, suzukiDF6D4RestorationTerm mode k := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hDigamma := summable_suzukiDF6D4DigammaSummand w
  have hRestoration : Summable
      (fun k : Nat => suzukiDF6D4RestorationTerm mode k) := by
    simpa only [Nat.zero_add] using
      summable_suzukiDF6D4RestorationTail mode 0
  have hDigammaValue :
      (Complex.digamma
        ((1 / 4 : Complex) +
          (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
            Complex.I)).im =
        ∑' n : Nat, suzukiDF6D4DigammaSummand n w := by
    convert suzukiDF6D4_digamma_im_eq_tsum w using 1 <;>
      simp only [w] <;> push_cast <;> ring
  change (∑' k : Nat,
      2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-suzukiDF6D4RestorationDecay k * t) *
          Real.sin (w * t))) = _
  rw [hDigammaValue, ← hDigamma.tsum_sub hRestoration]
  apply tsum_congr
  intro k
  exact two_mul_integral_restorationKernel_eq_digammaSummand_sub mode k

theorem summable_exp_neg_restorationDecay_mul {t : Real} (ht : 0 < t) :
    Summable (fun k : Nat =>
      Real.exp (-suzukiDF6D4RestorationDecay k * t)) := by
  let q : Real := Real.exp (-2 * t)
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact (Real.exp_lt_one_iff).2 (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeom := (hasSum_geometric_of_norm_lt_one hqnorm).summable.mul_left
    (Real.exp (-t / 2))
  exact hgeom.congr fun k => by
    dsimp only [q]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    unfold suzukiDF6D4RestorationDecay
    congr 1
    ring

theorem tsum_exp_neg_restorationDecay_mul {t : Real} (ht : 0 < t) :
    (∑' k : Nat, Real.exp (-suzukiDF6D4RestorationDecay k * t)) =
      Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := by
  let q : Real := Real.exp (-2 * t)
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact (Real.exp_lt_one_iff).2 (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeom := (hasSum_geometric_of_norm_lt_one hqnorm).mul_left
    (Real.exp (-t / 2))
  calc
    (∑' k : Nat, Real.exp (-suzukiDF6D4RestorationDecay k * t)) =
        ∑' k : Nat, Real.exp (-t / 2) * q ^ k := by
          apply tsum_congr
          intro k
          dsimp only [q]
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          unfold suzukiDF6D4RestorationDecay
          congr 1
          ring
    _ = Real.exp (-t / 2) * (1 - q)⁻¹ := hgeom.tsum_eq
    _ = Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := by
      simp only [q, div_eq_mul_inv]

theorem suzukiR1SecondKernel_eq_tsum_sub_of_pos
    {t : Real} (ht : 0 < t) :
    suzukiR1SecondKernel t =
      (∑' k : Nat, Real.exp (-suzukiDF6D4RestorationDecay k * t)) -
        1 / (2 * t) := by
  rw [suzukiR1SecondKernel, if_neg ht.ne', abs_of_pos ht]
  unfold suzukiR1SecondOffOrigin
  rw [tsum_exp_neg_restorationDecay_mul ht]

/-- After the exact termwise transform calculation, the archimedean identity
has only two analytic inputs left: the cancellation-aware sum/integral bridge
and the finite Dirichlet comparison normalization. -/
theorem suzukiDF6D4ArchimedeanIdentity_of_sumIntegral_and_comparison
    (mode : Nat)
    (hsumIntegral :
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiR1SecondKernel t *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
        (∑' k : Nat,
          ∫ t in (0 : Real)..2 * suzukiProjectAStar,
            Real.exp (-suzukiDF6D4RestorationDecay k * t) *
              Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) -
          ∫ t in (0 : Real)..2 * suzukiProjectAStar,
            (1 / (2 * t)) *
              Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))
    (hcomparison :
      suzukiDF6D4ComparisonSineTransform mode =
        -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          (1 / (2 * t)) *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))) :
    -((Complex.digamma
        ((1 / 4 : Complex) +
          (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
            Complex.I)).im -
        ∑' k : Nat, suzukiDF6D4RestorationTerm mode k) -
        suzukiDF6D4ComparisonSineTransform mode =
      -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiR1SecondKernel t *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) := by
  have hseries :=
    tsum_two_mul_integral_restorationKernel_eq_digamma_im_sub mode
  have hscaled :
      (Complex.digamma
        ((1 / 4 : Complex) +
          (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
            Complex.I)).im -
          ∑' k : Nat, suzukiDF6D4RestorationTerm mode k =
        2 * (∑' k : Nat,
          ∫ t in (0 : Real)..2 * suzukiProjectAStar,
            Real.exp (-suzukiDF6D4RestorationDecay k * t) *
              Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) := by
    rw [← tsum_mul_left]
    exact hseries.symm
  rw [hscaled, hcomparison, hsumIntegral]
  ring

/-- The elementary pole transform reduces the full smooth identity to the
archimedean `r₁''` transform identity. -/
theorem suzukiDF6D4SmoothTransformDifference_eq_integral_of_archimedean
    (mode : Nat)
    (harchimedean :
      -((Complex.digamma
          ((1 / 4 : Complex) +
            (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
              Complex.I)).im -
          ∑' k : Nat, suzukiDF6D4RestorationTerm mode k) -
          suzukiDF6D4ComparisonSineTransform mode =
        -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiR1SecondKernel t *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))) :
    suzukiDF6D4SmoothTransformDifference mode =
      -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiRSecondKernel t *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  let poleKernel : Real → Real := fun t =>
    -(Real.exp (t / 2) + Real.exp (-t / 2))
  have hSinContinuous : Continuous (fun t : Real => Real.sin (w * t)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hPoleContinuous : Continuous poleKernel := by
    dsimp only [poleKernel]
    exact ((Real.continuous_exp.comp (continuous_id.div_const 2)).add
      (Real.continuous_exp.comp
        (continuous_id.neg.div_const 2))).neg
  have hPoleIntegrable : IntervalIntegrable
      (fun t => poleKernel t * Real.sin (w * t)) volume
      0 (2 * suzukiProjectAStar) :=
    (hPoleContinuous.mul hSinContinuous).intervalIntegrable _ _
  have hGammaIntegrable : IntervalIntegrable
      (fun t => suzukiR1SecondKernel t * Real.sin (w * t)) volume
      0 (2 * suzukiProjectAStar) :=
    (continuous_suzukiR1SecondKernel.mul hSinContinuous).intervalIntegrable _ _
  have hKernelIntegral :
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiRSecondKernel t * Real.sin (w * t)) =
        (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          poleKernel t * Real.sin (w * t)) +
        (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiR1SecondKernel t * Real.sin (w * t)) := by
    calc
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiRSecondKernel t * Real.sin (w * t)) =
          ∫ t in (0 : Real)..2 * suzukiProjectAStar,
            (poleKernel t * Real.sin (w * t) +
              suzukiR1SecondKernel t * Real.sin (w * t)) := by
            apply intervalIntegral.integral_congr
            intro t _
            change suzukiRSecondKernel t * Real.sin (w * t) =
              poleKernel t * Real.sin (w * t) +
                suzukiR1SecondKernel t * Real.sin (w * t)
            rw [suzukiRSecondKernel_eq_pole_add_gamma]
            dsimp only [poleKernel]
            ring
      _ = _ := intervalIntegral.integral_add hPoleIntegrable hGammaIntegrable
  have hPole := suzukiDF6D4PoleSineTransform_eq_kernel_integral mode
  have hDecomposition :
      suzukiDF6D4SmoothTransformDifference mode =
        suzukiDF6D4PoleSineTransform mode +
          (-((Complex.digamma
            ((1 / 4 : Complex) +
              (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
                Complex.I)).im -
            ∑' k : Nat, suzukiDF6D4RestorationTerm mode k) -
            suzukiDF6D4ComparisonSineTransform mode) := by
    unfold suzukiDF6D4SmoothTransformDifference
      suzukiDF6D4CompleteSineTransform
    ring
  dsimp only [w, poleKernel] at hKernelIntegral
  rw [hDecomposition, hPole, harchimedean, hKernelIntegral]
  ring

theorem suzukiDF6D4SmoothTransformDifference_abs_le_of_archimedean
    (mode : Nat) (hmode : 1 ≤ mode)
    (harchimedean :
      -((Complex.digamma
          ((1 / 4 : Complex) +
            (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
              Complex.I)).im -
          ∑' k : Nat, suzukiDF6D4RestorationTerm mode k) -
          suzukiDF6D4ComparisonSineTransform mode =
        -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiR1SecondKernel t *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))) :
    |suzukiDF6D4SmoothTransformDifference mode| ≤
      (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
        Real.pi) / mode := by
  exact suzukiDF6D4SmoothTransformDifference_abs_le_of_transformIdentity
    mode hmode
      (suzukiDF6D4SmoothTransformDifference_eq_integral_of_archimedean
        mode harchimedean)

end

end RiemannHypothesisProject.Experiments.M100
