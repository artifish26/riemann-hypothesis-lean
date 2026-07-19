import RiemannHypothesisProject.RiemannWeilShiftedRadius.FiniteComponentSourceImageCertificates

/-!
# Shifted-radius certificate endpoints

This module contains weighted-to-exact certificate handoffs, cutoff-zero-data
constructors, abstract polynomial p-series endpoints, and dense/source target
summability wrappers for the shifted-radius route.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion
open MeasureTheory
open scoped Topology

namespace RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
The weighted zero-locus estimate implies the exact-norm shifted-radius bound
at every Riemann-Weil zero argument.
-/
theorem zeroArgument_norm_le_shiftedRadialBound
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system) :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        certificate.constant f *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              certificate.decayExponent) := by
  intro f rho
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let radiusPower : Real := (norm zeroArgument + 2) ^ certificate.decayExponent
  have hbase_pos : 0 < norm zeroArgument + 2 := by
    have hnorm_nonneg : 0 <= norm zeroArgument := norm_nonneg zeroArgument
    linarith
  have hradiusPower_pos : 0 < radiusPower := by
    dsimp [radiusPower]
    exact Real.rpow_pos_of_pos hbase_pos certificate.decayExponent
  have hweighted :
      norm (system.extension f zeroArgument) * radiusPower <=
        certificate.constant f := by
    simpa [zeroArgument, radiusPower] using
      certificate.zeroArgument_weighted_norm_le f rho
  have hdiv :
      norm (system.extension f zeroArgument) * radiusPower / radiusPower <=
        certificate.constant f / radiusPower :=
    div_le_div_of_nonneg_right hweighted (le_of_lt hradiusPower_pos)
  have hleft :
      norm (system.extension f zeroArgument) * radiusPower / radiusPower =
        norm (system.extension f zeroArgument) := by
    field_simp [hradiusPower_pos.ne']
  have hright :
      certificate.constant f / radiusPower =
        certificate.constant f * (1 / radiusPower) := by
    ring
  calc
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex)))
        = norm (system.extension f zeroArgument) := by
          rfl
    _ = norm (system.extension f zeroArgument) * radiusPower / radiusPower := by
      rw [hleft]
    _ <= certificate.constant f / radiusPower := hdiv
    _ = certificate.constant f * (1 / radiusPower) := hright
    _ = certificate.constant f *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            certificate.decayExponent) := by
      rfl

/-- Convert a weighted zero-locus certificate to the exact-norm zero-locus certificate. -/
noncomputable def toZeroArgumentShiftedRadiusDecayCertificate
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system) :
    RiemannWeilZeroArgumentShiftedRadiusDecayCertificate system where
  constant := certificate.constant
  decayExponent := certificate.decayExponent
  constant_nonneg := certificate.constant_nonneg
  decayExponent_nonneg := certificate.decayExponent_nonneg
  zeroArgument_norm_le_shiftedRadialBound :=
    certificate.zeroArgument_norm_le_shiftedRadialBound

/--
The weighted zero-locus certificate directly feeds cutoff-1 closed-ball
p-series zero data.
-/
noncomputable def toCutoffOneClosedBallZeroData
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  certificate.toZeroArgumentShiftedRadiusDecayCertificate
    |>.toCutoffOneClosedBallZeroData counting counting_cutoff_eq
      growth_add_one_lt_decay

/--
The weighted shifted-radius zero-locus estimate gives the closed-ball cutoff-1
direct p-series shell bound for the real zero-side weight.

This is the proof-bearing core of the direct-weight p-series bridge: it combines
`norm (system.weight f rho) <= norm (system.zeroValue f rho)`, the weighted
shifted-radius certificate, and the closed-ball first-entry lower-radius
comparison.
-/
theorem norm_weight_le_closedBall_cutoffOneShellBound
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.weight f rho) <=
      certificate.constant f *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ certificate.decayExponent) := by
  let n :=
    ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho
  change
    norm (system.weight f rho) <=
      certificate.constant f *
        (1 / |(((n - 1 : Nat) : Real) + 1)| ^
          certificate.decayExponent)
  have hweight_le_extension :
      norm (system.weight f rho) <=
        norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) := by
    simpa [SchwartzRiemannWeilExtensionSystem.zeroValue] using
      system.norm_weight_le_norm_zeroValue f rho
  have hshifted :
      norm (system.weight f rho) <=
        certificate.constant f *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              certificate.decayExponent) :=
    hweight_le_extension.trans
      (certificate.zeroArgument_norm_le_shiftedRadialBound f rho)
  by_cases hn : 1 <= n
  · have hindex : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    have hlower :
        closedBallZeroArgumentShellLowerBound ((n - 1) + 1) <
          norm (riemannWeilZeroArgument (rho : Complex)) := by
      simpa [n, hindex] using
        closedBallZero_firstEntryIndex_argumentShellLowerBound_lt rho
    have hfactor :
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              certificate.decayExponent) <=
          (1 / |((n - 1 : Nat) : Real) + 1| ^
            certificate.decayExponent) :=
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_tailFactor_of_succ_argumentShellLowerBound
        (n - 1) certificate.decayExponent_nonneg hlower
    exact hshifted.trans
      (by
        simpa [n] using
          mul_le_mul_of_nonneg_left hfactor
            (certificate.constant_nonneg f))
  · have hn_zero : n = 0 := by omega
    have hfactor :
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              certificate.decayExponent) <= 1 :=
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_one_of_nonneg_radius
        (norm_nonneg (riemannWeilZeroArgument (rho : Complex)))
        certificate.decayExponent_nonneg
    have hprefix :
        certificate.constant f *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                certificate.decayExponent) <=
          certificate.constant f :=
      (mul_le_mul_of_nonneg_left hfactor
          (certificate.constant_nonneg f)).trans_eq
        (mul_one (certificate.constant f))
    exact hshifted.trans
      (by
        simpa [n, hn_zero] using hprefix)

/--
The weighted shifted-radius certificate gives a direct abstract polynomial
decay estimate for the real zero-side weight on closed-ball first-entry shells.

This keeps the restricted-source route on the real-valued weight: the proof
uses `norm_weight_le_closedBall_cutoffOneShellBound` as its shell-bound field.
-/
noncomputable def toAbstractPolynomialZeroDecayEstimate
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system) :
    SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
      ComplexCompactExhaustion.closedBallZero where
  weight := system.weight
  cutoff := 1
  shellBound := fun f n =>
    certificate.constant f *
      (1 / |(((n - 1 : Nat) : Real) + 1)| ^
        certificate.decayExponent)
  zeroConstant := certificate.constant
  decayExponent := fun _ => certificate.decayExponent
  zeroConstant_nonneg := certificate.constant_nonneg
  shellBound_nonneg := by
    intro f n
    exact mul_nonneg (certificate.constant_nonneg f)
      (one_div_nonneg.mpr
        (Real.rpow_nonneg
          (abs_nonneg ((((n - 1 : Nat) : Real) + 1)))
          certificate.decayExponent))
  tail_shellBound_le := by
    intro f n
    dsimp
    simp
  norm_weight_le_shellBound := by
    intro f rho
    exact certificate.norm_weight_le_closedBall_cutoffOneShellBound f rho

/--
The weighted shifted-radius certificate and closed-ball polynomial counting
produce the separated direct-weight p-series input.
-/
noncomputable def toAbstractSeparatedPolynomialDecayEstimate
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent) :
    SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate
      ComplexCompactExhaustion.closedBallZero :=
  SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
    counting
    certificate.toAbstractPolynomialZeroDecayEstimate
    (by
      simpa [toAbstractPolynomialZeroDecayEstimate] using counting_cutoff_eq)
    (fun _f => by
      simpa [toAbstractPolynomialZeroDecayEstimate] using
        growth_add_one_lt_decay)

/--
The weighted shifted-radius certificate and closed-ball polynomial counting
produce the abstract polynomial-cardinality decay-tail majorant for
`system.weight`.
-/
noncomputable def toAbstractPolynomialCardDecayTailMajorant
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent) :
    SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
      ComplexCompactExhaustion.closedBallZero :=
  (certificate.toAbstractSeparatedPolynomialDecayEstimate counting
    counting_cutoff_eq growth_add_one_lt_decay)
    |>.toEventualPolynomialCardDecayTailMajorant

/--
The weighted shifted-radius certificate plus cutoff-1 closed-ball polynomial
counting gives absolute summability of the real zero-side weight.
-/
theorem summable_norm_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) := by
  simpa [toAbstractSeparatedPolynomialDecayEstimate,
    toAbstractPolynomialZeroDecayEstimate,
    SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay] using
    (certificate.toAbstractSeparatedPolynomialDecayEstimate counting
      counting_cutoff_eq growth_add_one_lt_decay).summable_norm_weight f

/--
The weighted shifted-radius certificate plus cutoff-1 closed-ball polynomial
counting makes the real zero-side weight summable.
-/
theorem summable_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) := by
  simpa [toAbstractSeparatedPolynomialDecayEstimate,
    toAbstractPolynomialZeroDecayEstimate,
    SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay] using
    (certificate.toAbstractSeparatedPolynomialDecayEstimate counting
      counting_cutoff_eq growth_add_one_lt_decay).summable_weight f

/--
The weighted shifted-radius certificate plus cutoff-1 closed-ball polynomial
counting gives the canonical infinite-series convergence for the norm of
`system.weight`.
-/
theorem hasSum_norm_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (f : SchwartzLineTestFunction) :
    HasSum
      (fun rho : ZetaZeroSubtype => norm (system.weight f rho))
      (tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho))) :=
  (certificate.summable_norm_weight_of_closedBallPolynomialCounting
    counting counting_cutoff_eq growth_add_one_lt_decay f).hasSum

/--
The weighted shifted-radius certificate plus cutoff-1 closed-ball polynomial
counting gives the canonical infinite-series convergence for `system.weight`.
-/
theorem hasSum_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (f : SchwartzLineTestFunction) :
    HasSum
      (system.weight f)
      (tsum (fun rho : ZetaZeroSubtype => system.weight f rho)) :=
  (certificate.summable_weight_of_closedBallPolynomialCounting
    counting counting_cutoff_eq growth_add_one_lt_decay f).hasSum

/--
The direct abstract zero side induced by a weighted shifted-radius certificate
has exactly the extension-system candidate weight.
-/
theorem directWeightZeroSide_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    (certificate.toAbstractSeparatedPolynomialDecayEstimate counting
      counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.weight f rho =
      system.weight f rho := by
  simpa [toAbstractSeparatedPolynomialDecayEstimate,
    toAbstractPolynomialZeroDecayEstimate,
    SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay] using
    (certificate.toAbstractSeparatedPolynomialDecayEstimate counting
      counting_cutoff_eq growth_add_one_lt_decay).toZeroSide_weight f rho

/--
Compact-exhaustion window sums converge for the direct abstract zero side
induced by a weighted shifted-radius certificate and cutoff-1 counting.
-/
theorem tendsto_directWeightZeroSide_windowZeroSide_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        (certificate.toAbstractSeparatedPolynomialDecayEstimate counting
          counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.windowZeroSide
            windowExhaustion n f)
      Filter.atTop
      (nhds
        ((certificate.toAbstractSeparatedPolynomialDecayEstimate counting
          counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.zeroSide f)) :=
  (certificate.toAbstractSeparatedPolynomialDecayEstimate counting
    counting_cutoff_eq growth_add_one_lt_decay).tendsto_windowZeroSide
      windowExhaustion f

/--
The direct abstract zero side induced by a weighted shifted-radius certificate
has global value equal to the concrete infinite sum of `system.weight`.
-/
theorem directWeightZeroSide_zeroSide_eq_tsum_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (f : SchwartzLineTestFunction) :
    (certificate.toAbstractSeparatedPolynomialDecayEstimate counting
      counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.zeroSide f =
      tsum (fun rho : ZetaZeroSubtype => system.weight f rho) := by
  unfold SchwartzRiemannWeilZeroSide.zeroSide
    SchwartzRiemannWeilZeroSide.toGlobalZetaZeroSide
    GlobalZetaZeroSide.zeroSide
  apply tsum_congr
  intro rho
  exact
    certificate.directWeightZeroSide_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f rho

/--
Compact-exhaustion window sums from a weighted shifted-radius certificate
converge to the concrete infinite sum of `system.weight`.
-/
theorem tendsto_directWeightZeroSide_windowZeroSide_tsum_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        (certificate.toAbstractSeparatedPolynomialDecayEstimate counting
          counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.windowZeroSide
            windowExhaustion n f)
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) := by
  rw [← certificate.directWeightZeroSide_zeroSide_eq_tsum_weight_of_closedBallPolynomialCounting
    counting counting_cutoff_eq growth_add_one_lt_decay f]
  exact
    certificate.tendsto_directWeightZeroSide_windowZeroSide_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/--
The actual finite compact-window sums of `system.weight` converge to the
concrete infinite sum when a weighted shifted-radius certificate is paired with
cutoff-1 closed-ball polynomial counting.
-/
theorem tendsto_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (certificate.summable_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f)

/--
The actual finite compact-window sums of the norm of `system.weight` converge
to the concrete norm-weight infinite sum under the same shifted-radius
certificate and cutoff-1 counting hypotheses.
-/
theorem tendsto_norm_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (certificate.summable_norm_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f)

/--
The weighted shifted-radius certificate and cutoff-1 counting make the signed
tail outside growing compact zero windows vanish.
-/
theorem tendsto_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
          windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    certificate.tendsto_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat => tsum (fun rho : ZetaZeroSubtype => system.weight f rho))
        Filter.atTop
        (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/--
The norm of the signed finite-window error for `system.weight` tends to zero.
-/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) := by
  have htail :=
    certificate.tendsto_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f
  simpa using htail.norm

/--
For every positive tolerance, the signed finite-window approximation error for
`system.weight` is eventually smaller than that tolerance.
-/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      norm
        (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
          windowExhaustion.zetaZeroWindowSum n (system.weight f)) < ε := by
  simpa using
    (certificate.tendsto_weight_zetaZeroWindowErrorNorm_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f).eventually
      (Iio_mem_nhds hε)

/--
The weighted shifted-radius certificate and cutoff-1 counting make the absolute
norm tail outside growing compact zero windows vanish.
-/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    certificate.tendsto_norm_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/--
For every positive tolerance, the absolute norm tail outside growing compact
zero windows is eventually smaller than that tolerance.
-/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
        ε := by
  simpa using
    (certificate.tendsto_norm_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f).eventually
      (Iio_mem_nhds hε)

namespace RiemannWeilDenseCoreZeroLocusPSeriesTarget

/--
The dense-core target also feeds the source-image dense constructor after
packaging the chosen core as `GuinandWeilSourceTestFunctionClass.ofDenseCore`.
-/
noncomputable def toSourceDenseWeightedDecayCertificate
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofSourceDenseWeightedDecayOfContinuous
    (system := system) target.testData target.constant target.decayExponent
    target.constant_nonneg target.decayExponent_nonneg
    target.dense_admissible_image target.zeroArgument_extension_continuous
    target.constant_continuous
    (by
      intro g _hg rho
      simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
        target.core_zeroArgument_weighted_norm_le g.1 g.2 rho)

/-- Convert the dense-core target to the exact-norm zero-locus certificate. -/
noncomputable def toZeroArgumentShiftedRadiusDecayCertificate
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system) :
    RiemannWeilZeroArgumentShiftedRadiusDecayCertificate system :=
  target.toWeightedDecayCertificate.toZeroArgumentShiftedRadiusDecayCertificate

/-- Feed the dense-core target directly into cutoff-1 closed-ball zero data. -/
noncomputable def toCutoffOneClosedBallZeroData
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  target.toWeightedDecayCertificate.toCutoffOneClosedBallZeroData
    counting counting_cutoff_eq growth_add_one_lt_decay

/-- Dense-core weighted zero-locus targets give absolute summability of `system.weight`. -/
theorem summable_norm_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
  target.toWeightedDecayCertificate
    |>.summable_norm_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- Dense-core weighted zero-locus targets make `system.weight` summable. -/
theorem summable_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  target.toWeightedDecayCertificate
    |>.summable_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- Dense-core targets give the canonical series convergence for `norm (system.weight f rho)`. -/
theorem hasSum_norm_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    HasSum
      (fun rho : ZetaZeroSubtype => norm (system.weight f rho))
      (tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho))) :=
  target.toWeightedDecayCertificate
    |>.hasSum_norm_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- Dense-core targets give the canonical series convergence for `system.weight f`. -/
theorem hasSum_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    HasSum
      (system.weight f)
      (tsum (fun rho : ZetaZeroSubtype => system.weight f rho)) :=
  target.toWeightedDecayCertificate
    |>.hasSum_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- The direct zero side induced by a dense-core target has candidate weight. -/
theorem directWeightZeroSide_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
      counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.weight
        f rho =
      system.weight f rho :=
  target.toWeightedDecayCertificate
    |>.directWeightZeroSide_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f rho

/-- Compact-window sums converge for the direct zero side induced by a dense-core target. -/
theorem tendsto_directWeightZeroSide_windowZeroSide_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
          counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.windowZeroSide
            windowExhaustion n f)
      Filter.atTop
      (nhds
        ((target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
          counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.zeroSide f)) :=
  target.toWeightedDecayCertificate
    |>.tendsto_directWeightZeroSide_windowZeroSide_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- The direct zero side induced by a dense-core target has concrete `system.weight` sum. -/
theorem directWeightZeroSide_zeroSide_eq_tsum_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
      counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.zeroSide f =
      tsum (fun rho : ZetaZeroSubtype => system.weight f rho) :=
  target.toWeightedDecayCertificate
    |>.directWeightZeroSide_zeroSide_eq_tsum_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- Compact-window sums from a dense-core target converge to the concrete weight sum. -/
theorem tendsto_directWeightZeroSide_windowZeroSide_tsum_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
          counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.windowZeroSide
            windowExhaustion n f)
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  target.toWeightedDecayCertificate
    |>.tendsto_directWeightZeroSide_windowZeroSide_tsum_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- Actual compact-window sums of `system.weight` converge from a dense-core target. -/
theorem tendsto_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  target.toWeightedDecayCertificate
    |>.tendsto_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- Norm compact-window sums of `system.weight` converge from a dense-core target. -/
theorem tendsto_norm_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
  target.toWeightedDecayCertificate
    |>.tendsto_norm_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- The signed compact-window tail of `system.weight` vanishes from a dense-core target. -/
theorem tendsto_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
          windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds 0) :=
  target.toWeightedDecayCertificate
    |>.tendsto_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- The signed finite-window error norm vanishes from a dense-core target. -/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) :=
  target.toWeightedDecayCertificate
    |>.tendsto_weight_zetaZeroWindowErrorNorm_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- Dense-core targets give eventual epsilon control of signed finite-window error. -/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      norm
        (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
          windowExhaustion.zetaZeroWindowSum n (system.weight f)) < ε :=
  target.toWeightedDecayCertificate
    |>.eventually_weight_zetaZeroWindowErrorNorm_lt_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f hε

/-- The absolute norm compact-window tail of `system.weight` vanishes from a dense-core target. -/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) :=
  target.toWeightedDecayCertificate
    |>.tendsto_norm_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- Dense-core targets give eventual epsilon control of the absolute norm tail. -/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
        ε :=
  target.toWeightedDecayCertificate
    |>.eventually_norm_weight_zetaZeroWindowTail_lt_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f hε

end RiemannWeilDenseCoreZeroLocusPSeriesTarget

namespace RiemannWeilSourceImageZeroLocusPSeriesTarget

/-- Convert the source-image target to the exact-norm zero-locus certificate. -/
noncomputable def toZeroArgumentShiftedRadiusDecayCertificate
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system) :
    RiemannWeilZeroArgumentShiftedRadiusDecayCertificate system :=
  target.toWeightedDecayCertificate.toZeroArgumentShiftedRadiusDecayCertificate

/-- Feed the source-image target directly into cutoff-1 closed-ball zero data. -/
noncomputable def toCutoffOneClosedBallZeroData
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  target.toWeightedDecayCertificate.toCutoffOneClosedBallZeroData
    counting counting_cutoff_eq growth_add_one_lt_decay

/-- Source-image weighted zero-locus targets give absolute summability of `system.weight`. -/
theorem summable_norm_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
  target.toWeightedDecayCertificate
    |>.summable_norm_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- Source-image weighted zero-locus targets make `system.weight` summable. -/
theorem summable_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  target.toWeightedDecayCertificate
    |>.summable_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- Source-image targets give the canonical series convergence for `norm (system.weight f rho)`. -/
theorem hasSum_norm_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    HasSum
      (fun rho : ZetaZeroSubtype => norm (system.weight f rho))
      (tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho))) :=
  target.toWeightedDecayCertificate
    |>.hasSum_norm_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- Source-image targets give the canonical series convergence for `system.weight f`. -/
theorem hasSum_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    HasSum
      (system.weight f)
      (tsum (fun rho : ZetaZeroSubtype => system.weight f rho)) :=
  target.toWeightedDecayCertificate
    |>.hasSum_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- The direct zero side induced by a source-image target has candidate weight. -/
theorem directWeightZeroSide_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
      counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.weight
        f rho =
      system.weight f rho :=
  target.toWeightedDecayCertificate
    |>.directWeightZeroSide_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f rho

/-- Compact-window sums converge for the direct zero side induced by a source-image target. -/
theorem tendsto_directWeightZeroSide_windowZeroSide_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
          counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.windowZeroSide
            windowExhaustion n f)
      Filter.atTop
      (nhds
        ((target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
          counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.zeroSide f)) :=
  target.toWeightedDecayCertificate
    |>.tendsto_directWeightZeroSide_windowZeroSide_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- The direct zero side induced by a source-image target has concrete `system.weight` sum. -/
theorem directWeightZeroSide_zeroSide_eq_tsum_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
      counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.zeroSide f =
      tsum (fun rho : ZetaZeroSubtype => system.weight f rho) :=
  target.toWeightedDecayCertificate
    |>.directWeightZeroSide_zeroSide_eq_tsum_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- Compact-window sums from a source-image target converge to the concrete weight sum. -/
theorem tendsto_directWeightZeroSide_windowZeroSide_tsum_weight_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
          counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.windowZeroSide
            windowExhaustion n f)
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  target.toWeightedDecayCertificate
    |>.tendsto_directWeightZeroSide_windowZeroSide_tsum_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- Actual compact-window sums of `system.weight` converge from a source-image target. -/
theorem tendsto_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  target.toWeightedDecayCertificate
    |>.tendsto_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- Norm compact-window sums of `system.weight` converge from a source-image target. -/
theorem tendsto_norm_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
  target.toWeightedDecayCertificate
    |>.tendsto_norm_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- The signed compact-window tail of `system.weight` vanishes from a source-image target. -/
theorem tendsto_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
          windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds 0) :=
  target.toWeightedDecayCertificate
    |>.tendsto_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- The signed finite-window error norm vanishes from a source-image target. -/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) :=
  target.toWeightedDecayCertificate
    |>.tendsto_weight_zetaZeroWindowErrorNorm_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- Source-image targets give eventual epsilon control of signed finite-window error. -/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      norm
        (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
          windowExhaustion.zetaZeroWindowSum n (system.weight f)) < ε :=
  target.toWeightedDecayCertificate
    |>.eventually_weight_zetaZeroWindowErrorNorm_lt_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f hε

/-- The absolute norm compact-window tail of `system.weight` vanishes from a source-image target. -/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) :=
  target.toWeightedDecayCertificate
    |>.tendsto_norm_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/-- Source-image targets give eventual epsilon control of the absolute norm tail. -/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
        ε :=
  target.toWeightedDecayCertificate
    |>.eventually_norm_weight_zetaZeroWindowTail_lt_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f hε

end RiemannWeilSourceImageZeroLocusPSeriesTarget

namespace RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget

/-- Convert the finite-component source-image target to the exact-norm certificate. -/
noncomputable def toZeroArgumentShiftedRadiusDecayCertificate
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system) :
    RiemannWeilZeroArgumentShiftedRadiusDecayCertificate system :=
  target.toSourceImageZeroLocusPSeriesTarget
    |>.toZeroArgumentShiftedRadiusDecayCertificate

/-- Feed the finite-component source-image target into cutoff-1 closed-ball zero data. -/
noncomputable def toCutoffOneClosedBallZeroData
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  target.toSourceImageZeroLocusPSeriesTarget
    |>.toCutoffOneClosedBallZeroData counting counting_cutoff_eq
      growth_add_one_lt_decay

/--
Finite-component source-image targets give absolute summability of
`system.weight`.
-/
theorem summable_norm_weight_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
  target.toWeightedDecayCertificate
    |>.summable_norm_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- Finite-component source-image targets make `system.weight` summable. -/
theorem summable_weight_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  target.toWeightedDecayCertificate
    |>.summable_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/--
Finite-component source-image targets give the canonical series convergence
for `norm (system.weight f rho)`.
-/
theorem hasSum_norm_weight_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    HasSum
      (fun rho : ZetaZeroSubtype => norm (system.weight f rho))
      (tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho))) :=
  target.toWeightedDecayCertificate
    |>.hasSum_norm_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/--
Finite-component source-image targets give the canonical series convergence
for `system.weight f`.
-/
theorem hasSum_weight_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    HasSum
      (system.weight f)
      (tsum (fun rho : ZetaZeroSubtype => system.weight f rho)) :=
  target.toWeightedDecayCertificate
    |>.hasSum_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/-- The direct zero side induced by a finite-component source-image target has candidate weight. -/
theorem directWeightZeroSide_weight_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
      counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.weight
        f rho =
      system.weight f rho :=
  target.toWeightedDecayCertificate
    |>.directWeightZeroSide_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f rho

/--
Compact-window sums converge for the direct zero side induced by a
finite-component source-image target.
-/
theorem tendsto_directWeightZeroSide_windowZeroSide_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
          counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.windowZeroSide
            windowExhaustion n f)
      Filter.atTop
      (nhds
        ((target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
          counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.zeroSide f)) :=
  target.toWeightedDecayCertificate
    |>.tendsto_directWeightZeroSide_windowZeroSide_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/--
The direct zero side induced by a finite-component source-image target has
concrete `system.weight` sum.
-/
theorem directWeightZeroSide_zeroSide_eq_tsum_weight_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (f : SchwartzLineTestFunction) :
    (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
      counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.zeroSide f =
      tsum (fun rho : ZetaZeroSubtype => system.weight f rho) :=
  target.toWeightedDecayCertificate
    |>.directWeightZeroSide_zeroSide_eq_tsum_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay f

/--
Compact-window sums from a finite-component source-image target converge to
the concrete weight sum.
-/
theorem tendsto_directWeightZeroSide_windowZeroSide_tsum_weight_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        (target.toWeightedDecayCertificate.toAbstractSeparatedPolynomialDecayEstimate
          counting counting_cutoff_eq growth_add_one_lt_decay).toZeroSide.windowZeroSide
            windowExhaustion n f)
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  target.toWeightedDecayCertificate
    |>.tendsto_directWeightZeroSide_windowZeroSide_tsum_weight_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/--
Actual compact-window sums of `system.weight` converge from a finite-component
source-image target.
-/
theorem tendsto_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  target.toWeightedDecayCertificate
    |>.tendsto_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/--
Norm compact-window sums of `system.weight` converge from a finite-component
source-image target.
-/
theorem tendsto_norm_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
  target.toWeightedDecayCertificate
    |>.tendsto_norm_weight_zetaZeroWindowSum_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/--
The signed compact-window tail of `system.weight` vanishes from a
finite-component source-image target.
-/
theorem tendsto_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
          windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds 0) :=
  target.toWeightedDecayCertificate
    |>.tendsto_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/--
The signed finite-window error norm vanishes from a finite-component
source-image target.
-/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) :=
  target.toWeightedDecayCertificate
    |>.tendsto_weight_zetaZeroWindowErrorNorm_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/--
Finite-component source-image targets give eventual epsilon control of signed
finite-window error.
-/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      norm
        (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
          windowExhaustion.zetaZeroWindowSum n (system.weight f)) < ε :=
  target.toWeightedDecayCertificate
    |>.eventually_weight_zetaZeroWindowErrorNorm_lt_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f hε

/--
The absolute norm compact-window tail of `system.weight` vanishes from a
finite-component source-image target.
-/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) :=
  target.toWeightedDecayCertificate
    |>.tendsto_norm_weight_zetaZeroWindowTail_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f

/--
Finite-component source-image targets give eventual epsilon control of the
absolute norm tail.
-/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < target.decayExponent)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
        ε :=
  target.toWeightedDecayCertificate
    |>.eventually_norm_weight_zetaZeroWindowTail_lt_of_closedBallPolynomialCounting
      counting counting_cutoff_eq growth_add_one_lt_decay windowExhaustion f hε

end RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget

/--
If admissible source tests cover all project Schwartz tests, it is enough to
prove the weighted zero-locus estimate on the source class.
-/
noncomputable def ofSourceCoverageWeightedDecay
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (coversSchwartz :
      forall f : SchwartzLineTestFunction,
        exists g : testData.SourceTestFunction,
          testData.admissible g /\ testData.toSchwartz g = f)
    (source_zeroArgument_weighted_norm_le :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall rho : ZetaZeroSubtype,
            norm
                (system.extension (testData.toSchwartz g)
                  (riemannWeilZeroArgument (rho : Complex))) *
                (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                  decayExponent <=
              constant (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system where
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  zeroArgument_weighted_norm_le := by
    classical
    intro f rho
    let g := Classical.choose (coversSchwartz f)
    have hgpair := Classical.choose_spec (coversSchwartz f)
    have hg : testData.admissible g := hgpair.1
    have hgf : testData.toSchwartz g = f := hgpair.2
    simpa [g, hgf] using source_zeroArgument_weighted_norm_le g hg rho

/--
Finite-component source for a weighted zero-locus certificate.  The component
estimates only need to hold at Riemann-Weil zero arguments.
-/
noncomputable def ofFiniteComponentSumWeightedDecay
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (componentConstant : Index -> SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (componentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= componentConstant i f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_eq_component_sum_zeroArgument :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        system.extension f (riemannWeilZeroArgument (rho : Complex)) =
          Finset.univ.sum fun i : Index =>
            component i f (riemannWeilZeroArgument (rho : Complex)))
    (component_zeroArgument_weighted_norm_le :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
          norm
              (component i f (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                decayExponent <=
            componentConstant i f) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system where
  constant := fun f => Finset.univ.sum fun i : Index => componentConstant i f
  decayExponent := decayExponent
  constant_nonneg := by
    intro f
    exact Finset.sum_nonneg fun i _ => componentConstant_nonneg i f
  decayExponent_nonneg := decayExponent_nonneg
  zeroArgument_weighted_norm_le := by
    intro f rho
    let zeroArgument := riemannWeilZeroArgument (rho : Complex)
    let radiusPower : Real := (norm zeroArgument + 2) ^ decayExponent
    have hbase_pos : 0 < norm zeroArgument + 2 := by
      have hnorm_nonneg : 0 <= norm zeroArgument := norm_nonneg zeroArgument
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos decayExponent)
    have hnorm :
        norm (system.extension f zeroArgument) <=
          (Finset.univ.sum fun i : Index =>
            norm (component i f zeroArgument)) := by
      rw [show system.extension f zeroArgument =
          Finset.univ.sum fun i : Index => component i f zeroArgument by
        simpa [zeroArgument] using
          extension_eq_component_sum_zeroArgument f rho]
      exact norm_sum_le Finset.univ (fun i : Index => component i f zeroArgument)
    calc
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            decayExponent
          = norm (system.extension f zeroArgument) * radiusPower := by
            rfl
      _ <= (Finset.univ.sum fun i : Index =>
            norm (component i f zeroArgument)) * radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f zeroArgument) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => componentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [zeroArgument, radiusPower] using
            component_zeroArgument_weighted_norm_le i f rho

end RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate
