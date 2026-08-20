import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointSmoothTransformIdentity

/-!
# Cancellation-aware restoration sum/integral bridge for M100-DF6D4

This module exchanges the positive exponential restoration series with the
finite endpoint integral.  The apparent singularity at the origin is absorbed
by the already checked continuous extension of Suzuki's `r₁''` kernel.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set
open scoped BigOperators

theorem intervalIntegrable_suzukiDF6D4SingularSineKernel (mode : Nat) :
    IntervalIntegrable
      (fun t : Real =>
        (1 / (2 * t)) *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))
      volume 0 (2 * suzukiProjectAStar) := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hL : 0 < 2 * suzukiProjectAStar := by
    nlinarith [suzukiProjectAStar_pos]
  by_cases hw : w = 0
  · simp only [w] at hw
    simp [hw]
  have hcontinuous : Continuous
      (fun t : Real => (w / 2) * Real.sinc (w * t)) :=
    continuous_const.mul
      (Real.continuous_sinc.comp (continuous_const.mul continuous_id))
  apply (hcontinuous.intervalIntegrable 0 (2 * suzukiProjectAStar)).congr_uIoo
  intro t ht
  rw [uIoo_of_le hL.le] at ht
  have ht0 : t ≠ 0 := ht.1.ne'
  change w / 2 * Real.sinc (w * t) =
    1 / (2 * t) * Real.sin (w * t)
  rw [Real.sinc_of_ne_zero (mul_ne_zero hw ht0)]
  field_simp [hw, ht0]

theorem suzukiDF6D4Restoration_integral_tsum (mode : Nat) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (∑' k : Nat,
          Real.exp (-suzukiDF6D4RestorationDecay k * t)) *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
      ∑' k : Nat,
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          Real.exp (-suzukiDF6D4RestorationDecay k * t) *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t) := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  let F : Nat → Real → Real := fun k t =>
    Real.exp (-suzukiDF6D4RestorationDecay k * t) * Real.sin (w * t)
  let bound : Nat → Real → Real := fun k t =>
    |w| * t * Real.exp (-suzukiDF6D4RestorationDecay k * t)
  have hL : 0 < 2 * suzukiProjectAStar := by
    nlinarith [suzukiProjectAStar_pos]
  have hFMeasurable : ∀ k,
      AEStronglyMeasurable (F k)
        (volume.restrict (Set.uIoc (0 : Real)
          (2 * suzukiProjectAStar))) := by
    intro k
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        (Real.continuous_sin.comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hBound : ∀ k, ∀ᵐ t ∂(volume : Measure Real),
      t ∈ Set.uIoc (0 : Real) (2 * suzukiProjectAStar) →
        ‖F k t‖ ≤ bound k t := by
    intro k
    filter_upwards with t
    intro ht
    rw [uIoc_of_le hL.le] at ht
    have htpos : 0 < t := ht.1
    dsimp only [F, bound]
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-suzukiDF6D4RestorationDecay k * t) *
          |Real.sin (w * t)| ≤
        Real.exp (-suzukiDF6D4RestorationDecay k * t) * |w * t| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs
            (Real.exp_pos _).le
      _ = |w| * t *
          Real.exp (-suzukiDF6D4RestorationDecay k * t) := by
        rw [abs_mul, abs_of_pos htpos]
        ring
  have hBoundSummable : ∀ᵐ t ∂(volume : Measure Real),
      t ∈ Set.uIoc (0 : Real) (2 * suzukiProjectAStar) →
        Summable (fun k => bound k t) := by
    filter_upwards with t
    intro ht
    rw [uIoc_of_le hL.le] at ht
    have hsum := summable_exp_neg_restorationDecay_mul ht.1
    exact (hsum.mul_left (|w| * t)).congr fun k => by
      dsimp only [bound]
  have hBoundIntegrable : IntervalIntegrable
      (fun t => ∑' k : Nat, bound k t) volume
        0 (2 * suzukiProjectAStar) := by
    let g : Real → Real := fun t =>
      |w| * (t * suzukiR1SecondKernel t + 1 / 2)
    have hgContinuous : Continuous g := by
      dsimp only [g]
      exact continuous_const.mul
        ((continuous_id.mul continuous_suzukiR1SecondKernel).add
          continuous_const)
    apply (hgContinuous.intervalIntegrable
      0 (2 * suzukiProjectAStar)).congr_uIoo
    intro t ht
    rw [uIoo_of_le hL.le] at ht
    have htpos : 0 < t := ht.1
    have hfactor :
        (∑' k : Nat, bound k t) =
          (|w| * t) *
            ∑' k : Nat,
              Real.exp (-suzukiDF6D4RestorationDecay k * t) := by
      rw [← tsum_mul_left]
    change g t = ∑' k : Nat, bound k t
    rw [hfactor]
    dsimp only [g]
    rw [suzukiR1SecondKernel_eq_tsum_sub_of_pos htpos]
    field_simp [htpos.ne']
    ring
  have hLimit : ∀ᵐ t ∂(volume : Measure Real),
      t ∈ Set.uIoc (0 : Real) (2 * suzukiProjectAStar) →
        HasSum (fun k => F k t)
          ((∑' k : Nat,
            Real.exp (-suzukiDF6D4RestorationDecay k * t)) *
              Real.sin (w * t)) := by
    filter_upwards with t
    intro ht
    rw [uIoc_of_le hL.le] at ht
    simpa only [F] using
      (summable_exp_neg_restorationDecay_mul ht.1).hasSum.mul_right
        (Real.sin (w * t))
  have hinterchange :=
    intervalIntegral.hasSum_integral_of_dominated_convergence
      (a := (0 : Real)) (b := 2 * suzukiProjectAStar) (μ := volume)
      bound hFMeasurable hBound hBoundSummable hBoundIntegrable hLimit
  change (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      (∑' k : Nat,
        Real.exp (-suzukiDF6D4RestorationDecay k * t)) *
        Real.sin (w * t)) = _
  simpa only [F] using hinterchange.tsum_eq.symm

theorem suzukiDF6D4R1_sumIntegral_decomposition (mode : Nat) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiR1SecondKernel t *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
      (∑' k : Nat,
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          Real.exp (-suzukiDF6D4RestorationDecay k * t) *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) -
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          (1 / (2 * t)) *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t) := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  let series : Real → Real := fun t =>
    (∑' k : Nat,
      Real.exp (-suzukiDF6D4RestorationDecay k * t)) * Real.sin (w * t)
  let singular : Real → Real := fun t =>
    (1 / (2 * t)) * Real.sin (w * t)
  have hL : 0 < 2 * suzukiProjectAStar := by
    nlinarith [suzukiProjectAStar_pos]
  have hSingular : IntervalIntegrable singular volume
      0 (2 * suzukiProjectAStar) := by
    simpa only [singular, w] using
      intervalIntegrable_suzukiDF6D4SingularSineKernel mode
  have hKernel : IntervalIntegrable
      (fun t => suzukiR1SecondKernel t * Real.sin (w * t)) volume
        0 (2 * suzukiProjectAStar) :=
    (continuous_suzukiR1SecondKernel.mul
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hSeries : IntervalIntegrable series volume
      0 (2 * suzukiProjectAStar) := by
    apply (hKernel.add hSingular).congr_uIoo
    intro t ht
    rw [uIoo_of_le hL.le] at ht
    have htpos : 0 < t := ht.1
    dsimp only [series, singular]
    rw [suzukiR1SecondKernel_eq_tsum_sub_of_pos htpos]
    field_simp [htpos.ne']
    ring
  have hsplit :
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiR1SecondKernel t * Real.sin (w * t)) =
        (∫ t in (0 : Real)..2 * suzukiProjectAStar, series t) -
          ∫ t in (0 : Real)..2 * suzukiProjectAStar, singular t := by
    rw [← intervalIntegral.integral_sub hSeries hSingular]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    by_cases ht0 : t = 0
    · subst t
      simp [series, singular]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      dsimp only [series, singular]
      rw [suzukiR1SecondKernel_eq_tsum_sub_of_pos htpos]
      field_simp [htpos.ne']
      ring
  rw [hsplit]
  have hinterchange := suzukiDF6D4Restoration_integral_tsum mode
  change (∫ t in (0 : Real)..2 * suzukiProjectAStar, series t) -
      (∫ t in (0 : Real)..2 * suzukiProjectAStar, singular t) = _
  rw [show (∫ t in (0 : Real)..2 * suzukiProjectAStar, series t) =
      ∑' k : Nat,
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          Real.exp (-suzukiDF6D4RestorationDecay k * t) *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t) by
    simpa only [series, w] using hinterchange]

/-- Once the cancellation-aware restoration exchange is supplied by this
module, only the finite Dirichlet comparison normalization remains in the
archimedean identity. -/
theorem suzukiDF6D4ArchimedeanIdentity_of_comparison
    (mode : Nat)
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
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) :=
  suzukiDF6D4ArchimedeanIdentity_of_sumIntegral_and_comparison mode
    (suzukiDF6D4R1_sumIntegral_decomposition mode) hcomparison

end

end RiemannHypothesisProject.Experiments.M100
