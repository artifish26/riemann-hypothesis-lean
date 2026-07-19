import RiemannHypothesisProject.RiemannWeilPointwiseRadialPSeriesBridge

/-!
# Antitone radial p-series bridge

`RiemannWeilPointwiseRadialPSeriesBridge` asks for a direct pointwise transfer
from a radius lower bound to an eventual p-series shell bound.  This file gives
an even more analytic-shaped route: prove that the radial majorant is antitone
in the radius, and prove the p-series bound at the checked shell lower bound.

The bridge then derives the pointwise transfer automatically.
-/

namespace RiemannHypothesisProject

open Filter
open ComplexCompactExhaustion

/--
Antitone radial p-series data for the standard closed-ball exhaustion.

The remaining source-shaped obligations are now separated into:

* `radialBound_antitone`, the radial decay/monotonicity theorem;
* `radialBound_lowerBound_le_eventualPSeries`, the value of that bound at the
  checked shell lower radius.
-/
structure RiemannWeilAntitoneRadialPSeriesEnvelopeData where
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
  radialBound_antitone :
    forall f : SchwartzLineTestFunction, Antitone (radialBound f)
  radialBound_lowerBound_le_eventualPSeries :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      radialBound f (closedBallZeroArgumentShellLowerBound n) <=
        SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
          cutoff prefixBound zeroConstant decayExponent f n
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero
  counting_cutoff_eq : counting.cutoff = cutoff
  growth_add_one_lt_decay :
    counting.growth + 1 < decayExponent

namespace RiemannWeilAntitoneRadialPSeriesEnvelopeData

/--
Antitone radial decay derives the pointwise radial-to-shell transfer whenever
the radius is past the checked shell lower bound.
-/
theorem radialBound_le_eventualPSeries_of_lowerBound
    (data : RiemannWeilAntitoneRadialPSeriesEnvelopeData)
    (f : SchwartzLineTestFunction)
    (n : Nat)
    (r : Real)
    (hlower : closedBallZeroArgumentShellLowerBound n < r) :
    data.radialBound f r <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
        data.cutoff data.prefixBound data.zeroConstant data.decayExponent f n := by
  have hle : closedBallZeroArgumentShellLowerBound n <= r := le_of_lt hlower
  exact
    ((data.radialBound_antitone f) hle).trans
      (data.radialBound_lowerBound_le_eventualPSeries f n)

/-- Antitone radial data specializes to pointwise radial p-series data. -/
noncomputable def toPointwiseRadialPSeriesEnvelopeData
    (data : RiemannWeilAntitoneRadialPSeriesEnvelopeData) :
    RiemannWeilPointwiseRadialPSeriesEnvelopeData where
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
  radialBound_le_eventualPSeries_of_lowerBound :=
    data.radialBound_le_eventualPSeries_of_lowerBound
  counting := data.counting
  counting_cutoff_eq := data.counting_cutoff_eq
  growth_add_one_lt_decay := data.growth_add_one_lt_decay

/-- Antitone radial data specializes to the zero-specific radial p-series data. -/
noncomputable def toRadialPSeriesEnvelopeData
    (data : RiemannWeilAntitoneRadialPSeriesEnvelopeData) :
    RiemannWeilRadialPSeriesEnvelopeData :=
  data.toPointwiseRadialPSeriesEnvelopeData.toRadialPSeriesEnvelopeData

/-- Convert antitone radial data to the existing eventual p-series zero-data package. -/
noncomputable def toEventualPSeriesEnvelopeZeroData
    (data : RiemannWeilAntitoneRadialPSeriesEnvelopeData) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  data.toPointwiseRadialPSeriesEnvelopeData.toEventualPSeriesEnvelopeZeroData

/-- The antitone radial package gives the exact shell-index envelope bound. -/
theorem envelope_zeroArgument_le_eventualConstantPSeries
    (data : RiemannWeilAntitoneRadialPSeriesEnvelopeData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
        data.cutoff data.prefixBound data.zeroConstant data.decayExponent f
        (closedBallZero.zetaZeroFirstEntryIndex rho) :=
  data.toPointwiseRadialPSeriesEnvelopeData.envelope_zeroArgument_le_eventualConstantPSeries
    f rho

/-- The induced shell-decay package from antitone radial p-series data. -/
noncomputable def shellDecay
    (data : RiemannWeilAntitoneRadialPSeriesEnvelopeData) :
    SchwartzRiemannWeilExtensionShellDecayEstimate closedBallZero data.system :=
  data.toEventualPSeriesEnvelopeZeroData.shellDecay

/-- The induced zero side from antitone radial p-series data. -/
noncomputable def zeroSide
    (data : RiemannWeilAntitoneRadialPSeriesEnvelopeData) :
    SchwartzRiemannWeilZeroSide :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide

/-- The induced zero side uses the candidate Riemann-Weil extension weight. -/
theorem zeroSide_weight
    (data : RiemannWeilAntitoneRadialPSeriesEnvelopeData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.zeroSide.weight f rho = data.system.weight f rho :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide_weight f rho

/-- Compact-exhaustion sums for the antitone radial-decay zero side converge globally. -/
theorem tendsto_windowZeroSide
    (data : RiemannWeilAntitoneRadialPSeriesEnvelopeData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.zeroSide.zeroSide f)) :=
  data.toEventualPSeriesEnvelopeZeroData.tendsto_windowZeroSide
    windowExhaustion f

end RiemannWeilAntitoneRadialPSeriesEnvelopeData

end RiemannHypothesisProject
