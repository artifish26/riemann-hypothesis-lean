import RiemannHypothesisProject.RiemannWeilZeroArgumentGeometry
import RiemannHypothesisProject.SchwartzRiemannWeilPSeriesConstantDecay

/-!
# Radial decay bridge for the Riemann-Weil p-series route

Analytic estimates for a complex extension are often stated as radial decay in
the Riemann-Weil zero argument.  The p-series endpoint in this project needs a
bound indexed by the closed-ball first-entry shell.  This file packages that
translation:

1. a radial envelope bound for `riemannWeilZeroArgument rho`;
2. a shell-transfer bound using the checked lower bound for that argument norm;
3. a conversion into the existing eventual p-series zero-data package.

No analytic decay theorem is proved here.  The point is to make the remaining
proof obligation narrower and source-shaped.
-/

namespace RiemannHypothesisProject

open Filter
open ComplexCompactExhaustion

/--
Radial-decay data sufficient to feed the eventual p-series envelope route for
the standard closed-ball exhaustion.

The field `radialBound_le_eventualPSeries_of_argumentLowerBound` is deliberately
given the checked geometric lower bound as an explicit hypothesis.  Future
analytic work can prove it from monotonicity of a concrete radial majorant
without reproving shell geometry.
-/
structure RiemannWeilRadialPSeriesEnvelopeData where
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
  radialBound_le_eventualPSeries_of_argumentLowerBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      ComplexCompactExhaustion.closedBallZeroArgumentShellLowerBound
          (closedBallZero.zetaZeroFirstEntryIndex rho) <
        ‖riemannWeilZeroArgument (rho : Complex)‖ ->
      radialBound f ‖riemannWeilZeroArgument (rho : Complex)‖ <=
        SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
          cutoff prefixBound zeroConstant decayExponent f
          (closedBallZero.zetaZeroFirstEntryIndex rho)
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero
  counting_cutoff_eq : counting.cutoff = cutoff
  growth_add_one_lt_decay :
    counting.growth + 1 < decayExponent

namespace RiemannWeilRadialPSeriesEnvelopeData

/--
The radial-decay package gives the exact shell-index envelope bound expected by
the constant-decay p-series constructor.
-/
theorem envelope_zeroArgument_le_eventualConstantPSeries
    (data : RiemannWeilRadialPSeriesEnvelopeData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
        data.cutoff data.prefixBound data.zeroConstant data.decayExponent f
        (closedBallZero.zetaZeroFirstEntryIndex rho) := by
  exact
    (data.envelope_le_radialBound f rho).trans
      (data.radialBound_le_eventualPSeries_of_argumentLowerBound f rho
        (closedBallZero_firstEntryIndex_argumentShellLowerBound_lt rho))

/-- Convert radial-decay data to the existing eventual p-series zero-data package. -/
noncomputable def toEventualPSeriesEnvelopeZeroData
    (data : RiemannWeilRadialPSeriesEnvelopeData) :
  SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofCountingAndEventualPSeriesEnvelopeBoundConstantDecay
      data.growthBound
      data.cutoff
      data.prefixBound
      data.zeroConstant
      data.decayExponent
      data.zeroConstant_nonneg
      data.prefixBound_nonneg
      data.envelope_zeroArgument_le_eventualConstantPSeries
      data.counting
      data.counting_cutoff_eq
      data.growth_add_one_lt_decay

/-- The induced shell-decay package from radial p-series data. -/
noncomputable def shellDecay
    (data : RiemannWeilRadialPSeriesEnvelopeData) :
    SchwartzRiemannWeilExtensionShellDecayEstimate closedBallZero data.system :=
  data.toEventualPSeriesEnvelopeZeroData.shellDecay

/-- The induced zero side from radial p-series data. -/
noncomputable def zeroSide
    (data : RiemannWeilRadialPSeriesEnvelopeData) :
    SchwartzRiemannWeilZeroSide :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide

/-- The induced zero side uses the candidate Riemann-Weil extension weight. -/
theorem zeroSide_weight
    (data : RiemannWeilRadialPSeriesEnvelopeData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.zeroSide.weight f rho = data.system.weight f rho :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide_weight f rho

/-- Compact-exhaustion sums for the radial-decay zero side converge globally. -/
theorem tendsto_windowZeroSide
    (data : RiemannWeilRadialPSeriesEnvelopeData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.zeroSide.zeroSide f)) :=
  data.toEventualPSeriesEnvelopeZeroData.tendsto_windowZeroSide
    windowExhaustion f

end RiemannWeilRadialPSeriesEnvelopeData

end RiemannHypothesisProject
