import RiemannHypothesisProject.GuinandWeilConcrete.PrimeCutoff

/-!
# Residual-side cutoff facts for concrete Guinand-Weil formulae

This module contains residual-side cutoff stabilization and convergence facts
assembled from prime, pole, and gamma side behavior.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

/--
If the prime cutoffs eventually stabilize, the whole concrete residual side
eventually stabilizes, because the pole and gamma cutoffs are constant.
-/
theorem eventually_guinandWeilTruncatedResidualSide_eq_residualSide_of_eventually_primeSide_eq
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (hprime :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedPrimeSide cutoff f = guinandWeilPrimeSide f) :
    ∀ᶠ cutoff : Nat in atTop,
      guinandWeilTruncatedResidualSide system cutoff f =
        guinandWeilResidualSide system f := by
  filter_upwards [hprime] with cutoff hcutoff
  simp [guinandWeilTruncatedResidualSide, guinandWeilResidualSide,
    guinandWeilTruncatedPoleSide, guinandWeilTruncatedGammaSide, hcutoff]

/--
Compact Fourier support makes the whole concrete residual cutoff eventually
equal to the limiting residual side.
-/
theorem eventually_guinandWeilTruncatedResidualSide_eq_residualSide_of_fourierCompactSupport
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (hf : GuinandWeilFourierCompactSupport f) :
    ∀ᶠ cutoff : Nat in atTop,
      guinandWeilTruncatedResidualSide system cutoff f =
        guinandWeilResidualSide system f :=
  eventually_guinandWeilTruncatedResidualSide_eq_residualSide_of_eventually_primeSide_eq
    system f
    (eventually_guinandWeilTruncatedPrimeSide_eq_primeSide_of_fourierCompactSupport f hf)

/--
An explicit compact Fourier support radius and tail-log cutoff make the whole
concrete residual side equal to its limiting value at that cutoff.
-/
theorem guinandWeilTruncatedResidualSide_eq_residualSide_of_fourierSupportRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (cutoff : Nat)
    (hcutoff :
      ∀ n : Nat, cutoff < n -> R < Real.log (n : Real)) :
    guinandWeilTruncatedResidualSide system cutoff f =
      guinandWeilResidualSide system f := by
  have hprime :
      guinandWeilTruncatedPrimeSide cutoff f = guinandWeilPrimeSide f :=
    guinandWeilTruncatedPrimeSide_eq_primeSide_of_fourierSupportRadius
      f hR_nonneg hsupport cutoff hcutoff
  simp [guinandWeilTruncatedResidualSide, guinandWeilResidualSide,
    guinandWeilTruncatedPoleSide, guinandWeilTruncatedGammaSide, hprime]

/--
The numeric cutoff condition `exp R < cutoff + 1` makes the whole concrete
residual side equal to its limiting value at that cutoff.
-/
theorem guinandWeilTruncatedResidualSide_eq_residualSide_of_fourierSupportRadius_exp_lt_succ
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (cutoff : Nat)
    (hcutoff : Real.exp R < ((cutoff + 1 : Nat) : Real)) :
    guinandWeilTruncatedResidualSide system cutoff f =
      guinandWeilResidualSide system f := by
  have hprime :
      guinandWeilTruncatedPrimeSide cutoff f = guinandWeilPrimeSide f :=
    guinandWeilTruncatedPrimeSide_eq_primeSide_of_fourierSupportRadius_exp_lt_succ
      f hR_nonneg hsupport cutoff hcutoff
  simp [guinandWeilTruncatedResidualSide, guinandWeilResidualSide,
    guinandWeilTruncatedPoleSide, guinandWeilTruncatedGammaSide, hprime]

/--
If the concrete prime component is summable, the positive-indexed prime cutoffs
converge to the corresponding `tsum`.
-/
theorem tendsto_guinandWeilTruncatedPrimeSide
    (f : SchwartzLineTestFunction)
    (hprime : Summable (fun n : Nat => guinandWeilPrimeTerm f n)) :
    Tendsto (fun cutoff : Nat => guinandWeilTruncatedPrimeSide cutoff f)
      atTop (𝓝 (guinandWeilPrimeSide f)) := by
  have hsum :
      Tendsto
        (fun cutoff : Nat =>
          (Finset.range (cutoff + 1)).sum
            (fun n : Nat => guinandWeilPrimeTerm f n))
        atTop (𝓝 (guinandWeilPrimeSide f)) := by
    simpa [guinandWeilPrimeSide, Function.comp_def] using
      hprime.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact hsum.congr'
    (Eventually.of_forall fun cutoff =>
      guinandWeilPrimeRangeSum_eq_truncatedPrimeSide cutoff f)

/-- The pole side cutoffs are constant, hence converge to the pole side. -/
theorem tendsto_guinandWeilTruncatedPoleSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun cutoff : Nat => guinandWeilTruncatedPoleSide system cutoff f)
      atTop (𝓝 (guinandWeilPoleSide system f)) := by
  simpa only [guinandWeilTruncatedPoleSide] using
    (tendsto_const_nhds : Tendsto (fun _ : Nat => guinandWeilPoleSide system f)
      atTop (𝓝 (guinandWeilPoleSide system f)))

/-- The gamma side cutoffs are constant, hence converge to the gamma side. -/
theorem tendsto_guinandWeilTruncatedGammaSide
    (f : SchwartzLineTestFunction) :
    Tendsto (fun cutoff : Nat => guinandWeilTruncatedGammaSide cutoff f)
      atTop (𝓝 (guinandWeilGammaSide f)) := by
  simpa only [guinandWeilTruncatedGammaSide] using
    (tendsto_const_nhds : Tendsto (fun _ : Nat => guinandWeilGammaSide f)
      atTop (𝓝 (guinandWeilGammaSide f)))

/-- The assembled truncated residual side converges when the prime component is summable. -/
theorem tendsto_guinandWeilTruncatedResidualSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (hprime : Summable (fun n : Nat => guinandWeilPrimeTerm f n)) :
    Tendsto (fun cutoff : Nat => guinandWeilTruncatedResidualSide system cutoff f)
      atTop (𝓝 (guinandWeilResidualSide system f)) := by
  simpa [guinandWeilTruncatedResidualSide, guinandWeilResidualSide] using
    ((tendsto_guinandWeilTruncatedPrimeSide f hprime).add
      (tendsto_guinandWeilTruncatedPoleSide system f)).add
        (tendsto_guinandWeilTruncatedGammaSide f)

/--
If the truncated residual side is eventually exactly the limiting residual
side, then its convergence does not need a separate summability argument.
-/
theorem tendsto_guinandWeilTruncatedResidualSide_of_eventually_eq
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (hresidual :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedResidualSide system cutoff f =
          guinandWeilResidualSide system f) :
    Tendsto (fun cutoff : Nat => guinandWeilTruncatedResidualSide system cutoff f)
      atTop (𝓝 (guinandWeilResidualSide system f)) :=
  (tendsto_const_nhds :
    Tendsto (fun _ : Nat => guinandWeilResidualSide system f)
      atTop (𝓝 (guinandWeilResidualSide system f))).congr'
        (hresidual.mono fun _ h => h.symm)

end

end RiemannHypothesisProject
