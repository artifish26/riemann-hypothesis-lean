import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaFourierLinearZeroDecay
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# M100-DF6F analytic admissibility of the smooth-core Burnol source

This module discharges the analytic side conditions surrounding the remaining
compact-support Guinand--Weil identity.  Compact support makes the
Fourier--Laplace source entire, and the already proved inverse-height estimate
gives absolute convergence of its completed-zero side.  No formula identity
is assumed or proved here.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory Filter Topology
open SchwartzLineTestFunction
open ComplexCompactExhaustion
open scoped ComplexConjugate

/-- A compactly supported Schwartz function remains integrable after
multiplication by a Fourier--Laplace exponential. -/
private theorem integrable_suzukiFourierSourceIntegrand_of_support_subset_Icc'
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Icc (-a) a) (z : Complex) :
    Integrable (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * v x) := by
  have hsub : Function.support
      (fun x : Real =>
        Complex.exp ((x : Complex) * Complex.I * z) * v x) ⊆
        Icc (-a) a := by
    intro x hx
    exact hsupport (fun hv => hx (by simp [hv]))
  apply (integrableOn_iff_integrable_of_support_subset hsub).mp
  exact (by fun_prop : Continuous (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * v x)).continuousOn
    |>.integrableOn_compact isCompact_Icc

/-- Differentiation under the compact-support Fourier--Laplace integral. -/
private theorem hasDerivAt_suzukiFourierSource_of_support_subset_Icc
    {a : Real} (ha : 0 ≤ a) {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Icc (-a) a) (z : Complex) :
    HasDerivAt (suzukiFourierSource v)
      (∫ x : Real,
        (Complex.exp ((x : Complex) * Complex.I * z) *
          ((x : Complex) * Complex.I)) * v x) z := by
  let s : Set Complex := Metric.ball z 1
  let F : Complex → Real → Complex := fun w x =>
    Complex.exp ((x : Complex) * Complex.I * w) * v x
  let F' : Complex → Real → Complex := fun w x =>
    (Complex.exp ((x : Complex) * Complex.I * w) *
      ((x : Complex) * Complex.I)) * v x
  let bound : Real → Real := fun x =>
    (a * Real.exp (a * (‖z‖ + 1))) * ‖v x‖
  have hs : s ∈ 𝓝 z := Metric.ball_mem_nhds z zero_lt_one
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) volume := by
    filter_upwards [] with w
    exact (by fun_prop : Continuous (F w)).aestronglyMeasurable
  have hFint : Integrable (F z) volume := by
    exact integrable_suzukiFourierSourceIntegrand_of_support_subset_Icc'
      hsupport z
  have hF'meas : AEStronglyMeasurable (F' z) volume := by
    exact (by fun_prop : Continuous (F' z)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂volume, ∀ w ∈ s, ‖F' w x‖ ≤ bound x := by
    filter_upwards with x
    intro w hw
    by_cases hvx : v x = 0
    · simp [F', bound, hvx]
    · have hx := hsupport hvx
      have hxabs : |x| ≤ a := by
        rw [abs_le]
        exact hx
      have hwNorm : ‖w‖ ≤ ‖z‖ + 1 := by
        have hdist : dist w z < 1 := by simpa [s] using hw
        have htriangle : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          calc
            ‖w‖ = ‖(w - z) + z‖ := by ring_nf
            _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        rw [dist_eq_norm] at hdist
        linarith
      have hexponent :
          (((x : Complex) * Complex.I * w).re) ≤
            a * (‖z‖ + 1) := by
        calc
          (((x : Complex) * Complex.I * w).re) ≤
              ‖(x : Complex) * Complex.I * w‖ :=
            Complex.re_le_norm _
          _ = |x| * ‖w‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              Complex.norm_I, mul_one]
          _ ≤ a * (‖z‖ + 1) :=
            mul_le_mul hxabs hwNorm (norm_nonneg _) ha
      dsimp only [F', bound]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one, Complex.norm_exp]
      calc
        Real.exp (↑x * Complex.I * w).re * |x| * ‖v x‖ ≤
            (Real.exp (a * (‖z‖ + 1)) * a) * ‖v x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (Real.exp_le_exp.mpr hexponent) hxabs
              (abs_nonneg x) (Real.exp_pos _).le) (norm_nonneg _)
        _ = a * Real.exp (a * (‖z‖ + 1)) * ‖v x‖ := by ring
  have hboundInt : Integrable bound volume := by
    exact v.integrable.norm.const_mul _
  have hdiff : ∀ᵐ x ∂volume, ∀ w ∈ s,
      HasDerivAt (F · x) (F' w x) w := by
    filter_upwards with x
    intro w _hw
    have hlinear : HasDerivAt
        (fun q : Complex => (x : Complex) * Complex.I * q)
        ((x : Complex) * Complex.I) w := by
      simpa using (hasDerivAt_id w).const_mul ((x : Complex) * Complex.I)
    have hexp := hlinear.cexp
    simpa only [F, F'] using hexp.mul_const (v x)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hFmeas hFint hF'meas hbound hboundInt hdiff
  change HasDerivAt
    (fun w => ∫ x : Real, F w x ∂volume) (∫ x : Real, F' z x ∂volume) z
  simpa only [F, F', suzukiFourierSource] using hmain.2

/-- The Fourier--Laplace transform of a compactly supported Schwartz function
is entire. -/
theorem differentiable_suzukiFourierSource_of_support_subset_Icc
    {a : Real} (ha : 0 ≤ a) {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Icc (-a) a) :
    Differentiable Complex (suzukiFourierSource v) := by
  intro z
  exact (hasDerivAt_suzukiFourierSource_of_support_subset_Icc
    ha hsupport z).differentiableAt

/-- The autocorrelation of a function supported in `[-a,a]` is supported in
`[-2a,2a]`. -/
theorem support_autocorrelation_subset_Icc_two_mul
    {a : Real} (ha : 0 ≤ a) {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Icc (-a) a) :
    Function.support (autocorrelation v) ⊆ Icc (-(2 * a)) (2 * a) := by
  intro x hx
  constructor
  · by_contra hnot
    have hlt : x < -(2 * a) := lt_of_not_ge hnot
    have habs : 2 * a < |x| := by
      rw [abs_of_neg (lt_of_lt_of_le hlt (neg_nonpos.mpr (mul_nonneg (by norm_num) ha)))]
      linarith
    exact hx (autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
      hsupport habs)
  · by_contra hnot
    have hlt : 2 * a < x := lt_of_not_ge hnot
    have habs : 2 * a < |x| := by
      rw [abs_of_nonneg (le_trans (mul_nonneg (by norm_num) ha) hlt.le)]
      exact hlt
    exact hx (autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
      hsupport habs)

/-- Burnol's Fourier--Laplace source attached to a smooth-core vector is
entire, with no source-theorem assumption. -/
theorem differentiable_burnolFourierLaplaceSource_suzukiProjectBase
    {a : Real} (ha : 0 ≤ a) (v : SuzukiSmoothCoreLinearSubmodule a) :
    Differentiable Complex
      (burnolFourierLaplaceSource (suzukiProjectBase v.1)) := by
  rw [show burnolFourierLaplaceSource (suzukiProjectBase v.1) =
      suzukiFourierSource (autocorrelation v.1) by
    funext z
    exact burnolFourierLaplaceSource_suzukiProjectBase v.1 z]
  exact differentiable_suzukiFourierSource_of_support_subset_Icc
    (mul_nonneg (by norm_num) ha)
    (support_autocorrelation_subset_Icc_two_mul ha
      (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩))

private theorem positiveOrdinateZetaZeroClampedHeight_functionalReflection'
    (rho : PositiveOrdinateZetaZeroSubtype) :
    positiveOrdinateZetaZeroClampedHeight
        (positiveOrdinateZetaZeroFunctionalReflection rho) =
      positiveOrdinateZetaZeroClampedHeight rho := by
  simp [positiveOrdinateZetaZeroClampedHeight,
    positiveOrdinateZetaZeroFunctionalReflection_value]

/-- One positive-ordinate Burnol zero weight is bounded by the inverse-square
majorant obtained from the two linear Fourier-decay factors. -/
private theorem norm_burnolNontrivialZeroWeight_positive_le
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (C : Real) (hC : 0 ≤ C)
    (hdecay : ∀ rho : PositiveOrdinateZetaZeroSubtype,
      ‖suzukiFourierSource v.1
          (suzukiSourceGammaArgument (rho : Complex))‖ ≤
            C / positiveOrdinateZetaZeroClampedHeight rho ∧
      ‖suzukiFourierSource v.1
          (suzukiSourceGammaArgument (conj (rho : Complex)))‖ ≤
            C / positiveOrdinateZetaZeroClampedHeight rho)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    ‖burnolNontrivialZeroWeight (suzukiProjectBase v.1)
        (positiveOrdinateToNontrivialZetaZero rho)‖ ≤
      C ^ 2 *
        (zetaZeroMultiplicityReal rho.1 /
          positiveOrdinateZetaZeroClampedHeight rho ^ 2) := by
  let rho' := positiveOrdinateZetaZeroFunctionalReflection rho
  let H := positiveOrdinateZetaZeroClampedHeight rho
  have hH : 0 < H := by
    dsimp [H, positiveOrdinateZetaZeroClampedHeight]
    exact zero_lt_one.trans_le (le_max_left 1 _)
  have hfirst := (hdecay rho').2
  rw [positiveOrdinateZetaZeroClampedHeight_functionalReflection'] at hfirst
  have hsecond := (hdecay rho).2
  have hsource :
      ‖burnolFourierLaplaceSource (suzukiProjectBase v.1)
          (riemannWeilZeroArgument (rho : Complex))‖ ≤
        (C / H) * (C / H) := by
    rw [burnolFourierLaplaceSource_suzukiProjectBase]
    rw [← suzukiSourceGammaArgument_conj_functionalReflection rho]
    rw [suzukiFourierSource_autocorrelation_at_gamma]
    rw [norm_mul, Complex.norm_conj]
    have harg :
        suzukiSourceGammaArgument
            (1 - conj (conj (rho' : Complex))) =
          suzukiSourceGammaArgument (conj (rho : Complex)) := by
      congr 1
      simp [rho', positiveOrdinateZetaZeroFunctionalReflection_value]
    rw [harg]
    exact mul_le_mul hfirst hsecond (norm_nonneg _) (by positivity)
  have hm : 0 ≤ zetaZeroMultiplicityReal rho.1 :=
    (zetaZeroMultiplicityReal_pos rho.1).le
  unfold burnolNontrivialZeroWeight positiveOrdinateToNontrivialZetaZero
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm]
  calc
    zetaZeroMultiplicityReal rho.1 *
        |(burnolFourierLaplaceSource (suzukiProjectBase v.1)
          (riemannWeilZeroArgument (rho : Complex))).re| ≤
        zetaZeroMultiplicityReal rho.1 *
          ‖burnolFourierLaplaceSource (suzukiProjectBase v.1)
            (riemannWeilZeroArgument (rho : Complex))‖ := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ ≤ zetaZeroMultiplicityReal rho.1 * ((C / H) * (C / H)) := by
      gcongr
    _ = C ^ 2 * (zetaZeroMultiplicityReal rho.1 / H ^ 2) := by
      field_simp
    _ = C ^ 2 *
        (zetaZeroMultiplicityReal rho.1 /
          positiveOrdinateZetaZeroClampedHeight rho ^ 2) := by rfl

/-- The conjugate negative-ordinate Burnol zero weight obeys the same
inverse-square majorant. -/
private theorem norm_burnolNontrivialZeroWeight_conjugate_le
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (C : Real) (hC : 0 ≤ C)
    (hdecay : ∀ rho : PositiveOrdinateZetaZeroSubtype,
      ‖suzukiFourierSource v.1
          (suzukiSourceGammaArgument (rho : Complex))‖ ≤
            C / positiveOrdinateZetaZeroClampedHeight rho ∧
      ‖suzukiFourierSource v.1
          (suzukiSourceGammaArgument (conj (rho : Complex)))‖ ≤
            C / positiveOrdinateZetaZeroClampedHeight rho)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    ‖burnolNontrivialZeroWeight (suzukiProjectBase v.1)
        (conjugatePositiveOrdinateToNontrivialZetaZero rho)‖ ≤
      C ^ 2 *
        (zetaZeroMultiplicityReal rho.1 /
          positiveOrdinateZetaZeroClampedHeight rho ^ 2) := by
  let rho' := positiveOrdinateZetaZeroFunctionalReflection rho
  let H := positiveOrdinateZetaZeroClampedHeight rho
  have hH : 0 < H := by
    dsimp [H, positiveOrdinateZetaZeroClampedHeight]
    exact zero_lt_one.trans_le (le_max_left 1 _)
  have hfirst := (hdecay rho').1
  rw [positiveOrdinateZetaZeroClampedHeight_functionalReflection'] at hfirst
  have hsecond := (hdecay rho).1
  have hsource :
      ‖burnolFourierLaplaceSource (suzukiProjectBase v.1)
          (riemannWeilZeroArgument (conj (rho : Complex)))‖ ≤
        (C / H) * (C / H) := by
    rw [burnolFourierLaplaceSource_suzukiProjectBase]
    rw [← suzukiSourceGammaArgument_functionalReflection rho]
    rw [suzukiFourierSource_autocorrelation_at_gamma]
    rw [norm_mul, Complex.norm_conj]
    have harg :
        suzukiSourceGammaArgument (1 - conj (rho' : Complex)) =
          suzukiSourceGammaArgument (rho : Complex) := by
      congr 1
      simp [rho', positiveOrdinateZetaZeroFunctionalReflection_value]
    rw [harg]
    exact mul_le_mul hfirst hsecond (norm_nonneg _) (by positivity)
  have hm : 0 ≤ zetaZeroMultiplicityReal rho.1 :=
    (zetaZeroMultiplicityReal_pos rho.1).le
  unfold burnolNontrivialZeroWeight
  unfold conjugatePositiveOrdinateToNontrivialZetaZero
  rw [zetaZeroMultiplicityReal, zetaZeroMultiplicity_conj]
  change ‖((zetaZeroMultiplicityReal rho.1) *
      (burnolFourierLaplaceSource (suzukiProjectBase v.1)
        (riemannWeilZeroArgument (conj (rho : Complex)))).re)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm]
  calc
    zetaZeroMultiplicityReal rho.1 *
        |(burnolFourierLaplaceSource (suzukiProjectBase v.1)
          (riemannWeilZeroArgument (conj (rho : Complex)))).re| ≤
        zetaZeroMultiplicityReal rho.1 *
          ‖burnolFourierLaplaceSource (suzukiProjectBase v.1)
            (riemannWeilZeroArgument (conj (rho : Complex)))‖ := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ ≤ zetaZeroMultiplicityReal rho.1 * ((C / H) * (C / H)) := by
      gcongr
    _ = C ^ 2 * (zetaZeroMultiplicityReal rho.1 / H ^ 2) := by
      field_simp
    _ = C ^ 2 *
        (zetaZeroMultiplicityReal rho.1 /
          positiveOrdinateZetaZeroClampedHeight rho ^ 2) := by rfl

/-- The completed Burnol zero side attached to every smooth-core vector is
absolutely summable, unconditionally. -/
theorem summable_norm_guinandWeilBurnolLiteratureZeroWeight_suzukiProjectBase
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Summable (fun rho : ZetaZeroSubtype =>
      ‖guinandWeilBurnolLiteratureZeroWeight
        (suzukiProjectBase v.1) rho‖) := by
  obtain ⟨C, hC, hdecay⟩ :=
    suzukiSourceAaSmoothCoreFourierLinearZeroDecay_proved v
  have hmajor :=
    unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable
      |>.mul_left (C ^ 2)
  have hpositive : Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      ‖burnolNontrivialZeroWeight (suzukiProjectBase v.1)
        (positiveOrdinateToNontrivialZetaZero rho)‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_burnolNontrivialZeroWeight_positive_le v C hC hdecay)
  have hconjugate : Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      ‖burnolNontrivialZeroWeight (suzukiProjectBase v.1)
        (conjugatePositiveOrdinateToNontrivialZetaZero rho)‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_burnolNontrivialZeroWeight_conjugate_le v C hC hdecay)
  have hsum : Summable (Sum.elim
      (fun rho : PositiveOrdinateZetaZeroSubtype =>
        ‖burnolNontrivialZeroWeight (suzukiProjectBase v.1)
          (positiveOrdinateToNontrivialZetaZero rho)‖)
      (fun rho : PositiveOrdinateZetaZeroSubtype =>
        ‖burnolNontrivialZeroWeight (suzukiProjectBase v.1)
          (conjugatePositiveOrdinateToNontrivialZetaZero rho)‖)) := by
    apply Summable.sum
    · simpa using hpositive
    · simpa using hconjugate
  have hnontrivial : Summable (fun rho : NontrivialZetaZeroSubtype =>
      ‖burnolNontrivialZeroWeight (suzukiProjectBase v.1) rho‖) := by
    apply nontrivialZetaZeroOrdinateEquiv.summable_iff.mp
    refine hsum.congr ?_
    intro i
    cases i <;> rfl
  let raw : ZetaZeroSubtype → Real := fun rho =>
    ‖guinandWeilBurnolLiteratureZeroWeight (suzukiProjectBase v.1) rho‖
  have hrestricted : Summable (fun rho : NontrivialZetaZeroSubtype =>
      raw rho.1) := by
    refine hnontrivial.congr ?_
    intro rho
    have hnotTrivial : ¬ IsTrivialZetaZero (rho : Complex) := rho.property
    simp [raw, burnolNontrivialZeroWeight,
      guinandWeilBurnolLiteratureZeroWeight, hnotTrivial]
  have hindicator : Summable (nontrivialZetaZeroSet.indicator raw) :=
    summable_subtype_iff_indicator.mp hrestricted
  refine hindicator.congr ?_
  intro rho
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · simp [raw, nontrivialZetaZeroSet,
      guinandWeilBurnolLiteratureZeroWeight, htrivial]
  · simp [raw, nontrivialZetaZeroSet,
      guinandWeilBurnolLiteratureZeroWeight, htrivial]

end

end RiemannHypothesisProject.Experiments.M100
