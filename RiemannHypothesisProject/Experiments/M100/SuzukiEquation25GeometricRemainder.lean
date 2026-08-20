import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25BoundedKernelPairing

/-!
# Geometric remainder beyond the exponential soft cutoff

The exact Gamma tail differs from its principal exponential reciprocal
cutoff by a fixed continuous kernel multiplied by `exp (-2 N |t|)`.  Hence
the difference vanishes in every finite-square source pairing.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ComplexConjugate Topology

/-- The fixed removable correction in the geometric denominator. -/
def suzukiEquation25GeometricCorrectionKernel (t : Real) : Real :=
  suzukiEquation25GammaTailKernel 0 t -
    suzukiEquation25SoftReciprocalKernel (1 / 2) t

theorem continuous_suzukiEquation25GeometricCorrectionKernel :
    Continuous suzukiEquation25GeometricCorrectionKernel :=
  (continuous_suzukiEquation25GammaTailKernel 0).sub
    (continuous_suzukiEquation25SoftReciprocalKernel (1 / 2))

@[simp]
theorem suzukiEquation25GeometricCorrectionKernel_zero :
    suzukiEquation25GeometricCorrectionKernel 0 = 1 / 2 := by
  simp [suzukiEquation25GeometricCorrectionKernel]
  norm_num

theorem suzukiEquation25GammaTailKernel_even (N : Nat) (t : Real) :
    suzukiEquation25GammaTailKernel N (-t) =
      suzukiEquation25GammaTailKernel N t := by
  unfold suzukiEquation25GammaTailKernel
    suzukiEquation25RawGammaExponentialPartial
    suzukiEquation25RawGammaExponentialKernel
    suzukiR1SecondKernel
  simp only [abs_neg, neg_eq_zero]

/-- Exact separation of the fixed geometric correction from the principal
soft reciprocal cutoff. -/
theorem suzukiEquation25GammaTailKernel_eq_soft_add_geometric
    (N : Nat) (t : Real) :
    suzukiEquation25GammaTailKernel N t =
      suzukiEquation25SoftReciprocalKernel
          (suzukiDF6D4RestorationDecay N) t +
        Real.exp (-(2 * (N : Real)) * |t|) *
          suzukiEquation25GeometricCorrectionKernel t := by
  by_cases ht : t = 0
  · subst t
    simp [suzukiDF6D4RestorationDecay]
    ring
  · have habs : 0 < |t| := abs_pos.mpr ht
    have htailN := suzukiEquation25GammaTailKernel_eq_of_pos habs N
    have htail0 := suzukiEquation25GammaTailKernel_eq_of_pos habs 0
    have hsoftN := suzukiEquation25SoftReciprocalKernel_eq_of_ne
      (lam := suzukiDF6D4RestorationDecay N) (t := t) ht
    have hsoft0 := suzukiEquation25SoftReciprocalKernel_eq_of_ne
      (lam := (1 / 2 : Real)) (t := t) ht
    have htailAbs : suzukiEquation25GammaTailKernel N t =
        suzukiEquation25GammaTailKernel N |t| := by
      rcases le_total 0 t with ht0 | ht0
      · rw [abs_of_nonneg ht0]
      · rw [abs_of_nonpos ht0]
        exact (suzukiEquation25GammaTailKernel_even N t).symm
    have htail0Abs : suzukiEquation25GammaTailKernel 0 t =
        suzukiEquation25GammaTailKernel 0 |t| := by
      rcases le_total 0 t with ht0 | ht0
      · rw [abs_of_nonneg ht0]
      · rw [abs_of_nonpos ht0]
        exact (suzukiEquation25GammaTailKernel_even 0 t).symm
    rw [htailAbs, htailN, hsoftN]
    unfold suzukiEquation25GeometricCorrectionKernel
    rw [htail0Abs, htail0, hsoft0]
    unfold suzukiDF6D4RestorationDecay
    have habsne : |t| ≠ 0 := ne_of_gt habs
    have hexpSplit :
        Real.exp (-(2 * (N : Real) + 1 / 2) * |t|) =
          Real.exp (-(2 * (N : Real)) * |t|) *
            Real.exp (-(1 / 2) * |t|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexpSplit]
    field_simp [habsne]
    ring

/-- The geometric correction vanishes in the finite-square pairing. -/
theorem tendsto_suzukiEquation25GeometricCorrectionPairing_zero
    {a : Real} (v : SuzukiSmoothCore a) :
    Tendsto
      (fun N : Nat =>
        suzukiFiniteKernelPairingComplex
          (fun t => Real.exp (-(2 * (N : Real)) * |t|) *
            suzukiEquation25GeometricCorrectionKernel t) a v.1)
      atTop (nhds 0) := by
  let mu : Measure (Real × Real) :=
    volume.restrict (suzukiFiniteSquare a)
  let majorant : Real × Real → Real := fun p =>
    ‖suzukiEquation25GeometricCorrectionKernel (p.1 - p.2)‖ *
      ‖v.1 p.2‖ * ‖v.1 p.1‖
  have hmajorant : Integrable majorant mu := by
    exact ((continuous_suzukiEquation25GeometricCorrectionKernel.norm.comp
      (by fun_prop : Continuous (fun p : Real × Real => p.1 - p.2))).mul
      (v.1.continuous.norm.comp (by fun_prop))).mul
      (v.1.continuous.norm.comp (by fun_prop))
      |>.continuousOn.integrableOn_compact
        (isCompact_suzukiFiniteSquare a)
  have hdiagFull : ∀ᵐ p : Real × Real, p.1 ≠ p.2 := by
    have hdiagMeas : MeasurableSet {p : Real × Real | p.1 ≠ p.2} :=
      (measurableSet_eq_fun measurable_fst measurable_snd).compl
    rw [Measure.volume_eq_prod,
      Measure.ae_prod_iff_ae_ae hdiagMeas]
    filter_upwards with x
    exact (volume.ae_ne x).mono fun y hy => Ne.symm hy
  have hdiag : ∀ᵐ p ∂mu, p.1 ≠ p.2 :=
    (ae_mono Measure.restrict_le_self) hdiagFull
  have hmeas : ∀ᶠ N : Nat in atTop, AEStronglyMeasurable
      (fun p : Real × Real =>
        (((Real.exp (-(2 * (N : Real)) * |p.1 - p.2|) *
          suzukiEquation25GeometricCorrectionKernel (p.1 - p.2)) : Real) :
            Complex) * v.1 p.2 * conj (v.1 p.1)) mu := by
    filter_upwards with N
    have hk : Continuous (fun t : Real =>
        Real.exp (-(2 * (N : Real)) * |t|) *
          suzukiEquation25GeometricCorrectionKernel t) :=
      (Real.continuous_exp.comp (by fun_prop)).mul
        continuous_suzukiEquation25GeometricCorrectionKernel
    exact (continuous_suzukiKernelPairingIntegrand hk v.1.continuous)
      |>.aestronglyMeasurable
  have hbound : ∀ᶠ N : Nat in atTop, ∀ᵐ p ∂mu,
      ‖((((Real.exp (-(2 * (N : Real)) * |p.1 - p.2|) *
          suzukiEquation25GeometricCorrectionKernel (p.1 - p.2)) : Real) :
            Complex) * v.1 p.2 * conj (v.1 p.1))‖ ≤ majorant p := by
    filter_upwards with N
    filter_upwards with p
    have hexp : Real.exp (-(2 * (N : Real)) * |p.1 - p.2|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have hN : 0 ≤ (N : Real) := Nat.cast_nonneg N
        have habs := abs_nonneg (p.1 - p.2)
        nlinarith)
    simp only [Complex.norm_mul, Complex.norm_real, Complex.norm_conj,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), majorant]
    have hrest : 0 ≤
        |suzukiEquation25GeometricCorrectionKernel (p.1 - p.2)| *
          ‖v.1 p.2‖ * ‖v.1 p.1‖ := by positivity
    simpa only [mul_assoc] using mul_le_of_le_one_left hrest hexp
  have hpoint : ∀ᵐ p ∂mu, Tendsto
      (fun N : Nat =>
        (((Real.exp (-(2 * (N : Real)) * |p.1 - p.2|) *
          suzukiEquation25GeometricCorrectionKernel (p.1 - p.2)) : Real) :
            Complex) * v.1 p.2 * conj (v.1 p.1))
      atTop (nhds 0) := by
    filter_upwards [hdiag] with p hp
    have habs : 0 < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr hp)
    have hdecay : Tendsto
        (fun N : Nat => Real.exp (-(2 * (N : Real)) * |p.1 - p.2|))
        atTop (nhds 0) := by
      have hbot : Tendsto
          (fun N : Nat => -(2 * (N : Real)) * |p.1 - p.2|)
          atTop atBot := by
        have hraw := tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg
          (by nlinarith : -(2 : Real) * |p.1 - p.2| < 0)
        convert hraw using 1
        funext N
        ring
      exact Real.tendsto_exp_atBot.comp hbot
    have hlim := ((hdecay.mul_const
      (suzukiEquation25GeometricCorrectionKernel (p.1 - p.2))).ofReal
        |>.mul_const (v.1 p.2 * conj (v.1 p.1)))
    have hlim0 : Tendsto
        (fun N : Nat =>
          (((Real.exp (-(2 * (N : Real)) * |p.1 - p.2|) *
            suzukiEquation25GeometricCorrectionKernel (p.1 - p.2)) : Real) :
              Complex) * (v.1 p.2 * conj (v.1 p.1)))
        atTop (nhds 0) := by
      simpa using hlim
    apply hlim0.congr'
    filter_upwards with N
    ring
  have hdct := tendsto_integral_filter_of_dominated_convergence
    majorant hmeas hbound hmajorant hpoint
  change Tendsto
    (fun N : Nat => ∫ p in suzukiFiniteSquare a,
      suzukiKernelPairingIntegrand
        (fun t => Real.exp (-(2 * (N : Real)) * |t|) *
          suzukiEquation25GeometricCorrectionKernel t) v.1 p)
    atTop (nhds 0)
  simpa [suzukiFiniteKernelPairingComplex,
    suzukiKernelPairingIntegrand] using hdct

end

end M100
end Experiments
end RiemannHypothesisProject
