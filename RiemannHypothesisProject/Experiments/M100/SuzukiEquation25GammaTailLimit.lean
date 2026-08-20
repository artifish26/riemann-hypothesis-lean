import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25SoftHardComparison

/-!
# Renormalized Gamma-tail limit for Suzuki's equation (2.5)

This module composes the normalized soft-kernel limit with the restoration
scale `2N + 1/2`, removes the asymptotically negligible logarithmic scale
error, and restores the exact Gamma tail through the vanishing geometric
correction.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Filter MeasureTheory Topology SchwartzLineTestFunction
open scoped Topology

theorem tendsto_suzukiDF6D4RestorationDecay_atTop :
    Tendsto (fun N : Nat => suzukiDF6D4RestorationDecay N)
      atTop atTop := by
  have hbase : Tendsto (fun N : Nat => 2 * (N : Real)) atTop atTop := by
    simpa [mul_comm] using
      tendsto_natCast_atTop_atTop.const_mul_atTop
        (by norm_num : (0 : Real) < 2)
  have hadd := hbase.atTop_add
    (tendsto_const_nhds (x := (1 / 2 : Real)))
  simpa [suzukiDF6D4RestorationDecay] using hadd

/-- The restoration scale differs from `2N` by a logarithmically negligible
factor. -/
theorem tendsto_log_suzukiDF6D4RestorationDecay_sub_log_sub_two :
    Tendsto
      (fun N : Nat =>
        Real.log (suzukiDF6D4RestorationDecay N) -
          Real.log N - Real.log 2)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun N : Nat => 1 / (N : Real)) atTop (nhds 0) :=
    by simpa [one_div] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := Real))
  have hquarterConst : Tendsto (fun _ : Nat => (1 / 4 : Real)) atTop
      (nhds (1 / 4 : Real)) := tendsto_const_nhds
  have hquarter := hquarterConst.mul hinv
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hratioRaw := hone.add hquarter
  have hratio : Tendsto
      (fun N : Nat =>
        suzukiDF6D4RestorationDecay N / (2 * (N : Real)))
      atTop (nhds 1) := by
    have hratio' : Tendsto
        (fun N : Nat =>
          suzukiDF6D4RestorationDecay N / (2 * (N : Real)))
        atTop (nhds (1 + (1 / 4 : Real) * 0)) := by
      apply hratioRaw.congr'
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      unfold suzukiDF6D4RestorationDecay
      field_simp [hN0]
      ring
    convert hratio' using 1 <;> ring
  have hlogRatio :=
    (Real.continuousAt_log (by norm_num : (1 : Real) ≠ 0)).tendsto.comp hratio
  have hlog : Tendsto
      (fun N : Nat =>
        Real.log (suzukiDF6D4RestorationDecay N) -
          Real.log N - Real.log 2)
      atTop (nhds (Real.log 1)) := by
    apply hlogRatio.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hdecayPos : 0 < suzukiDF6D4RestorationDecay N := by
      unfold suzukiDF6D4RestorationDecay
      positivity
    simp only [Function.comp_apply]
    rw [Real.log_div hdecayPos.ne'
      (mul_ne_zero (by norm_num : (2 : Real) ≠ 0) hN0)]
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hN0]
    ring
  simpa using hlog

/-- The renormalized Gamma-tail limit required by the finite-cancellation
reduction is now unconditional on every positive-radius smooth core. -/
theorem suzukiEquation25RenormalizedGammaTailLimitAt_proved (a : Real) :
    SuzukiEquation25RenormalizedGammaTailLimitAt a := by
  intro _ha v
  let mass : Real := ‖suzukiSmoothCoreToL2 v‖ ^ 2
  have hmass : mass = (autocorrelation v.1 0).re := by
    exact norm_sq_suzukiSmoothCoreToL2_eq_autocorrelation_zero_re v
  have hsoftDecay :=
    (tendsto_suzukiEquation25_softPairing_to_logFourier v).comp
      tendsto_suzukiDF6D4RestorationDecay_atTop
  have hlogCorrection :=
    tendsto_log_suzukiDF6D4RestorationDecay_sub_log_sub_two.neg.mul_const mass
  have hsoftSum := hlogCorrection.add hsoftDecay
  have hsoftNormalized : Tendsto
      (fun N : Nat =>
        (Real.log N + Real.eulerMascheroniConstant + Real.log 2) * mass +
          (suzukiFiniteKernelPairingComplex
            (suzukiEquation25SoftReciprocalKernel
              (suzukiDF6D4RestorationDecay N)) a v.1).re)
      atTop (nhds (suzukiSourceLogFourierForm v.1)) := by
    have hsoftSum' : Tendsto
        (fun N : Nat =>
          (Real.log N + Real.eulerMascheroniConstant + Real.log 2) * mass +
            (suzukiFiniteKernelPairingComplex
              (suzukiEquation25SoftReciprocalKernel
                (suzukiDF6D4RestorationDecay N)) a v.1).re)
        atTop
        (nhds (-0 * mass + suzukiSourceLogFourierForm v.1)) := by
      apply hsoftSum.congr'
      filter_upwards with N
      rw [hmass]
      simp only [Function.comp_apply]
      ring
    convert hsoftSum' using 1 <;> ring
  have hgeomComplex :=
    tendsto_suzukiEquation25GeometricCorrectionPairing_zero v
  have hgeom : Tendsto
      (fun N : Nat =>
        (suzukiFiniteKernelPairingComplex
          (fun t => Real.exp (-(2 * (N : Real)) * |t|) *
            suzukiEquation25GeometricCorrectionKernel t) a v.1).re)
      atTop (nhds 0) := by
    apply (Complex.continuous_re.continuousAt.tendsto.comp hgeomComplex).congr'
    filter_upwards with N
    rfl
  have hsum := hsoftNormalized.add hgeom
  have hpair : ∀ N : Nat,
      (suzukiFiniteKernelPairingComplex
          (suzukiEquation25GammaTailKernel N) a v.1).re =
        (suzukiFiniteKernelPairingComplex
          (suzukiEquation25SoftReciprocalKernel
            (suzukiDF6D4RestorationDecay N)) a v.1).re +
        (suzukiFiniteKernelPairingComplex
          (fun t => Real.exp (-(2 * (N : Real)) * |t|) *
            suzukiEquation25GeometricCorrectionKernel t) a v.1).re := by
    intro N
    have hkernel : suzukiEquation25GammaTailKernel N =
        fun t => suzukiEquation25SoftReciprocalKernel
            (suzukiDF6D4RestorationDecay N) t +
          Real.exp (-(2 * (N : Real)) * |t|) *
            suzukiEquation25GeometricCorrectionKernel t := by
      funext t
      exact suzukiEquation25GammaTailKernel_eq_soft_add_geometric N t
    rw [hkernel, suzukiFiniteKernelPairingComplex_add]
    · simp
    · exact continuous_suzukiEquation25SoftReciprocalKernel _
    · exact (by fun_prop : Continuous (fun t : Real =>
        Real.exp (-(2 * (N : Real)) * |t|))).mul
          continuous_suzukiEquation25GeometricCorrectionKernel
    · exact v.1.continuous
  have hfinal : Tendsto
      (fun N : Nat =>
        (Real.log N + Real.eulerMascheroniConstant + Real.log 2) * mass +
          (suzukiFiniteKernelPairingComplex
            (suzukiEquation25GammaTailKernel N) a v.1).re)
      atTop (nhds (suzukiSourceLogFourierForm v.1 + 0)) := by
    apply hsum.congr'
    filter_upwards with N
    rw [hpair N]
    ring
  simpa only [add_zero] using hfinal

/-- The proved tail limit closes the full scalar-free regular-kernel
correction used by the equation-(2.5) source bridge. -/
theorem suzukiEquation25RegularKernelCorrectionAt_proved (a : Real) :
    SuzukiEquation25RegularKernelCorrectionAt a :=
  suzukiEquation25RegularKernelCorrectionAt_of_renormalizedTailLimit
    (suzukiEquation25RenormalizedGammaTailLimitAt_proved a)

/-- The regular-kernel correction supplies the Gamma correction in the
spectral reduction of equation (2.5). -/
theorem suzukiEquation25GammaCorrectionAt_proved (a : Real) :
    SuzukiEquation25GammaCorrectionAt a :=
  suzukiEquation25GammaCorrectionAt_of_regularKernelCorrection
    (suzukiEquation25RegularKernelCorrectionAt_proved a)

/-- Equation (2.5), in the project normalization, is unconditional at every
positive source radius. -/
theorem suzukiEquation25SourceIdentityAt_proved (a : Real) :
    SuzukiEquation25SourceIdentityAt a :=
  (suzukiEquation25SourceIdentityAt_iff_gammaCorrection a).2
    (suzukiEquation25GammaCorrectionAt_proved a)

end

end M100
end Experiments
end RiemannHypothesisProject
