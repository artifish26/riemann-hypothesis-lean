import RiemannHypothesisProject.RiemannWeilRadialPSeriesBridge

/-!
# Pointwise radial-to-shell p-series bridge

`RiemannWeilRadialPSeriesBridge` packages a zero-specific radial transfer
hypothesis. This file gives a more source-shaped variant: prove a pointwise
bound for every shell index `n` and radius `r`, then Lean specializes it to the
actual Riemann-Weil zero argument of each zeta zero.

This is useful because future analytic estimates should usually prove
monotonic radial decay as a theorem about real radii, not as a theorem that
mentions zeta zeroes directly.
-/

namespace RiemannHypothesisProject

open Filter
open ComplexCompactExhaustion

/--
Pointwise radial p-series data for the standard closed-ball exhaustion.

The field `radialBound_le_eventualPSeries_of_lowerBound` is the remaining
source-shaped monotonicity/decay obligation: whenever a radius `r` is larger
than the checked lower bound for shell `n`, the radial majorant is bounded by
the shell's eventual p-series value.
-/
structure RiemannWeilPointwiseRadialPSeriesEnvelopeData where
  system : SchwartzRiemannWeilExtensionSystem
  growthBound : SchwartzRiemannWeilExtensionGrowthBound system
  cutoff : Nat
  prefixBound : SchwartzLineTestFunction -> Nat -> Real
  zeroConstant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  radialBound : SchwartzLineTestFunction -> Real -> Real
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  prefixBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n
  envelope_le_radialBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
        radialBound f ‖riemannWeilZeroArgument (rho : Complex)‖
  radialBound_le_eventualPSeries_of_lowerBound :
    forall (f : SchwartzLineTestFunction) (n : Nat) (r : Real),
      closedBallZeroArgumentShellLowerBound n < r ->
        radialBound f r <=
          SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
            cutoff prefixBound zeroConstant decayExponent f n
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero
  counting_cutoff_eq : counting.cutoff = cutoff
  growth_add_one_lt_decay :
    counting.growth + 1 < decayExponent

namespace RiemannWeilPointwiseRadialPSeriesEnvelopeData

/-- Pointwise radial data specializes to the zero-specific radial p-series package. -/
noncomputable def toRadialPSeriesEnvelopeData
    (data : RiemannWeilPointwiseRadialPSeriesEnvelopeData) :
    RiemannWeilRadialPSeriesEnvelopeData where
  system := data.system
  growthBound := data.growthBound
  cutoff := data.cutoff
  prefixBound := data.prefixBound
  zeroConstant := data.zeroConstant
  decayExponent := data.decayExponent
  radialBound := data.radialBound
  zeroConstant_nonneg := data.zeroConstant_nonneg
  prefixBound_nonneg := data.prefixBound_nonneg
  envelope_le_radialBound := data.envelope_le_radialBound
  radialBound_le_eventualPSeries_of_argumentLowerBound := fun f rho hlower =>
    data.radialBound_le_eventualPSeries_of_lowerBound f
      (closedBallZero.zetaZeroFirstEntryIndex rho)
      ‖riemannWeilZeroArgument (rho : Complex)‖
      hlower
  counting := data.counting
  counting_cutoff_eq := data.counting_cutoff_eq
  growth_add_one_lt_decay := data.growth_add_one_lt_decay

/-- Convert pointwise radial data to the existing eventual p-series zero-data package. -/
noncomputable def toEventualPSeriesEnvelopeZeroData
    (data : RiemannWeilPointwiseRadialPSeriesEnvelopeData) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  data.toRadialPSeriesEnvelopeData.toEventualPSeriesEnvelopeZeroData

/-- The pointwise radial package gives the exact shell-index envelope bound. -/
theorem envelope_zeroArgument_le_eventualConstantPSeries
    (data : RiemannWeilPointwiseRadialPSeriesEnvelopeData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
        data.cutoff data.prefixBound data.zeroConstant data.decayExponent f
        (closedBallZero.zetaZeroFirstEntryIndex rho) :=
  data.toRadialPSeriesEnvelopeData.envelope_zeroArgument_le_eventualConstantPSeries
    f rho

/-- The induced shell-decay package from pointwise radial p-series data. -/
noncomputable def shellDecay
    (data : RiemannWeilPointwiseRadialPSeriesEnvelopeData) :
    SchwartzRiemannWeilExtensionShellDecayEstimate closedBallZero data.system :=
  data.toEventualPSeriesEnvelopeZeroData.shellDecay

/-- The induced zero side from pointwise radial p-series data. -/
noncomputable def zeroSide
    (data : RiemannWeilPointwiseRadialPSeriesEnvelopeData) :
    SchwartzRiemannWeilZeroSide :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide

/-- The induced zero side uses the candidate Riemann-Weil extension weight. -/
theorem zeroSide_weight
    (data : RiemannWeilPointwiseRadialPSeriesEnvelopeData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.zeroSide.weight f rho = data.system.weight f rho :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide_weight f rho

/-- Compact-exhaustion sums for the pointwise radial-decay zero side converge globally. -/
theorem tendsto_windowZeroSide
    (data : RiemannWeilPointwiseRadialPSeriesEnvelopeData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.zeroSide.zeroSide f)) :=
  data.toEventualPSeriesEnvelopeZeroData.tendsto_windowZeroSide
    windowExhaustion f

end RiemannWeilPointwiseRadialPSeriesEnvelopeData

end RiemannHypothesisProject
