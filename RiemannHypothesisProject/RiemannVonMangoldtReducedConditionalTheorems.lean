import RiemannHypothesisProject.RiemannVonMangoldtConcretePublishedSources
import RiemannHypothesisProject.RiemannVonMangoldtCountingTarget
import RiemannHypothesisProject.SchwartzRiemannWeilReducedConditionalTheorems

/-!
# Riemann-von Mangoldt reduced conditional RH theorems

This module specializes the reduced constant-decay p-series route to the
standard closed-ball Riemann-von-Mangoldt zero-counting target. It also exposes
thin endpoints for published and fixed-error `N(T)` sources by routing them
through the named counting target. The remaining fields are still the actual
analytic work: the Riemann-von-Mangoldt counting target, a constant-decay
envelope inequality, the explicit formula, residual nonnegativity, and the
residual-positivity-to-RH implication.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion.ClosedBallZeroRiemannVonMangoldtCountingTarget

/--
Convert a closed-ball Riemann-von-Mangoldt counting target and a constant-decay
envelope estimate into eventual p-series zero data.
-/
noncomputable def toEventualPSeriesEnvelopeZeroDataConstantDecay
    (target :
      ComplexCompactExhaustion.ClosedBallZeroRiemannVonMangoldtCountingTarget)
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_zeroArgument_le_eventualConstantPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
            target.cutoff prefixBound zeroConstant decayExponent f
            (ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho))
    (growth_add_one_lt_decay : target.growth + 1 < decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofCountingAndEventualPSeriesEnvelopeBoundConstantDecay
    growthBound target.cutoff prefixBound zeroConstant decayExponent
    zeroConstant_nonneg prefixBound_nonneg
    envelope_zeroArgument_le_eventualConstantPSeries
    target.toPolynomialZeroCountingEstimate
    target.toPolynomialZeroCountingEstimate_cutoff
    (by
      rwa [target.toPolynomialZeroCountingEstimate_growth])

end ComplexCompactExhaustion.ClosedBallZeroRiemannVonMangoldtCountingTarget

section ClosedBallRiemannVonMangoldtConstantDecay

variable (target :
  ComplexCompactExhaustion.ClosedBallZeroRiemannVonMangoldtCountingTarget)
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
variable (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
variable (zeroConstant : SchwartzLineTestFunction -> Real)
variable (decayExponent : Real)
variable (zeroConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
variable (prefixBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
variable (envelope_zeroArgument_le_eventualConstantPSeries :
  forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
    growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
        target.cutoff prefixBound zeroConstant decayExponent f
        (ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho))
variable (growth_add_one_lt_decay : target.growth + 1 < decayExponent)
variable (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
variable (explicitFormula :
  forall f : SchwartzLineTestFunction,
    (target.toEventualPSeriesEnvelopeZeroDataConstantDecay
        growthBound prefixBound zeroConstant decayExponent
        zeroConstant_nonneg prefixBound_nonneg
        envelope_zeroArgument_le_eventualConstantPSeries
        growth_add_one_lt_decay).zeroSide.zeroSide f =
      primeSide f + poleSide f + gammaSide f)
variable (residual_nonneg :
  forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f)
variable (residual_positivity_implies_RHOn_univ :
  (forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f) ->
    RHOn (fun _ : Complex => True))

include target growthBound prefixBound zeroConstant decayExponent
  zeroConstant_nonneg prefixBound_nonneg
  envelope_zeroArgument_le_eventualConstantPSeries growth_add_one_lt_decay
  primeSide poleSide gammaSide explicitFormula residual_nonneg
  residual_positivity_implies_RHOn_univ

/--
Assemble a closed-ball Riemann-von-Mangoldt target and a constant-decay envelope
estimate into the compact eventual p-series formula-residual endpoint.
-/
noncomputable def eventualPSeriesInputDataOfRiemannVonMangoldtConstantDecayRawFormulaResidual :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  let zeroData :=
    target.toEventualPSeriesEnvelopeZeroDataConstantDecay
      growthBound prefixBound zeroConstant decayExponent zeroConstant_nonneg
      prefixBound_nonneg envelope_zeroArgument_le_eventualConstantPSeries
      growth_add_one_lt_decay
  SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData.ofZeroDataAndRawFormulaResidual
    zeroData primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

/--
A closed-ball Riemann-von-Mangoldt counting target plus constant-decay raw
formula-residual data proves universal local RH.
-/
theorem RHOn_univ_of_RiemannVonMangoldt_constantDecay_rawFormulaResidual :
    RHOn (fun _ : Complex => True) :=
  (eventualPSeriesInputDataOfRiemannVonMangoldtConstantDecayRawFormulaResidual
    (target := target)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHOn_univ

/--
A closed-ball Riemann-von-Mangoldt counting target plus constant-decay raw
formula-residual data proves the project RH statement.
-/
theorem RHStatement_of_RiemannVonMangoldt_constantDecay_rawFormulaResidual :
    RiemannHypothesisProject.RHStatement :=
  (eventualPSeriesInputDataOfRiemannVonMangoldtConstantDecayRawFormulaResidual
    (target := target)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHStatement

/--
A closed-ball Riemann-von-Mangoldt counting target plus constant-decay raw
formula-residual data proves Mathlib's `RiemannHypothesis`.
-/
theorem mathlib_RH_of_RiemannVonMangoldt_constantDecay_rawFormulaResidual :
    RiemannHypothesis :=
  (eventualPSeriesInputDataOfRiemannVonMangoldtConstantDecayRawFormulaResidual
    (target := target)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).mathlib_RH

end ClosedBallRiemannVonMangoldtConstantDecay

section PublishedRiemannVonMangoldtConstantDecay

variable (publishedCounting :
  ComplexCompactExhaustion.PublishedExplicitRiemannVonMangoldtSource)
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
variable (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
variable (zeroConstant : SchwartzLineTestFunction -> Real)
variable (decayExponent : Real)
variable (zeroConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
variable (prefixBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
variable (envelope_zeroArgument_le_eventualConstantPSeries :
  forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
    growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
        publishedCounting.toRiemannVonMangoldtCountingTarget.cutoff
        prefixBound zeroConstant decayExponent f
        (ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho))
variable (growth_add_one_lt_decay :
  publishedCounting.toRiemannVonMangoldtCountingTarget.growth + 1 <
    decayExponent)
variable (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
variable (explicitFormula :
  forall f : SchwartzLineTestFunction,
    (publishedCounting.toRiemannVonMangoldtCountingTarget
      |>.toEventualPSeriesEnvelopeZeroDataConstantDecay
        growthBound prefixBound zeroConstant decayExponent
        zeroConstant_nonneg prefixBound_nonneg
        envelope_zeroArgument_le_eventualConstantPSeries
        growth_add_one_lt_decay).zeroSide.zeroSide f =
      primeSide f + poleSide f + gammaSide f)
variable (residual_nonneg :
  forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f)
variable (residual_positivity_implies_RHOn_univ :
  (forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f) ->
    RHOn (fun _ : Complex => True))

include publishedCounting growthBound prefixBound zeroConstant decayExponent
  zeroConstant_nonneg prefixBound_nonneg
  envelope_zeroArgument_le_eventualConstantPSeries growth_add_one_lt_decay
  primeSide poleSide gammaSide explicitFormula residual_nonneg
  residual_positivity_implies_RHOn_univ

/--
Assemble a published explicit `N(T)` source, after conversion to the named
Riemann-von-Mangoldt target, with constant-decay raw formula-residual data.
-/
noncomputable def
    eventualPSeriesInputDataOfPublishedRiemannVonMangoldtConstantDecayRawFormulaResidual :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  eventualPSeriesInputDataOfRiemannVonMangoldtConstantDecayRawFormulaResidual
    (target := publishedCounting.toRiemannVonMangoldtCountingTarget)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)

/--
A published explicit `N(T)` source plus constant-decay raw formula-residual
data proves universal local RH.
-/
theorem RHOn_univ_of_publishedRiemannVonMangoldt_constantDecay_rawFormulaResidual :
    RHOn (fun _ : Complex => True) :=
  (eventualPSeriesInputDataOfPublishedRiemannVonMangoldtConstantDecayRawFormulaResidual
    (publishedCounting := publishedCounting)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHOn_univ

/--
A published explicit `N(T)` source plus constant-decay raw formula-residual
data proves the project RH statement.
-/
theorem RHStatement_of_publishedRiemannVonMangoldt_constantDecay_rawFormulaResidual :
    RiemannHypothesisProject.RHStatement :=
  (eventualPSeriesInputDataOfPublishedRiemannVonMangoldtConstantDecayRawFormulaResidual
    (publishedCounting := publishedCounting)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHStatement

/--
A published explicit `N(T)` source plus constant-decay raw formula-residual
data proves Mathlib's `RiemannHypothesis`.
-/
theorem mathlib_RH_of_publishedRiemannVonMangoldt_constantDecay_rawFormulaResidual :
    RiemannHypothesis :=
  (eventualPSeriesInputDataOfPublishedRiemannVonMangoldtConstantDecayRawFormulaResidual
    (publishedCounting := publishedCounting)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).mathlib_RH

end PublishedRiemannVonMangoldtConstantDecay

section FixedErrorRiemannVonMangoldtConstantDecay

variable {validFrom : Real} {publishedErrorTerm : Real -> Real}
variable (publishedCounting :
  ComplexCompactExhaustion.FixedErrorExplicitRiemannVonMangoldtSourceInput
    validFrom publishedErrorTerm)
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
variable (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
variable (zeroConstant : SchwartzLineTestFunction -> Real)
variable (decayExponent : Real)
variable (zeroConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
variable (prefixBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
variable (envelope_zeroArgument_le_eventualConstantPSeries :
  forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
    growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
        publishedCounting.toRiemannVonMangoldtCountingTarget.cutoff
        prefixBound zeroConstant decayExponent f
        (ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho))
variable (growth_add_one_lt_decay :
  publishedCounting.toRiemannVonMangoldtCountingTarget.growth + 1 <
    decayExponent)
variable (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
variable (explicitFormula :
  forall f : SchwartzLineTestFunction,
    (publishedCounting.toRiemannVonMangoldtCountingTarget
      |>.toEventualPSeriesEnvelopeZeroDataConstantDecay
        growthBound prefixBound zeroConstant decayExponent
        zeroConstant_nonneg prefixBound_nonneg
        envelope_zeroArgument_le_eventualConstantPSeries
        growth_add_one_lt_decay).zeroSide.zeroSide f =
      primeSide f + poleSide f + gammaSide f)
variable (residual_nonneg :
  forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f)
variable (residual_positivity_implies_RHOn_univ :
  (forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f) ->
    RHOn (fun _ : Complex => True))

include publishedCounting growthBound prefixBound zeroConstant decayExponent
  zeroConstant_nonneg prefixBound_nonneg
  envelope_zeroArgument_le_eventualConstantPSeries growth_add_one_lt_decay
  primeSide poleSide gammaSide explicitFormula residual_nonneg
  residual_positivity_implies_RHOn_univ

/--
Assemble a fixed-error published `N(T)` source, after conversion to the named
Riemann-von-Mangoldt target, with constant-decay raw formula-residual data.
-/
noncomputable def
    eventualPSeriesInputDataOfFixedErrorRiemannVonMangoldtConstantDecayRawFormulaResidual :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  eventualPSeriesInputDataOfRiemannVonMangoldtConstantDecayRawFormulaResidual
    (target := publishedCounting.toRiemannVonMangoldtCountingTarget)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)

/--
A fixed-error published `N(T)` source plus constant-decay raw formula-residual
data proves universal local RH.
-/
theorem RHOn_univ_of_fixedErrorRiemannVonMangoldt_constantDecay_rawFormulaResidual :
    RHOn (fun _ : Complex => True) :=
  (eventualPSeriesInputDataOfFixedErrorRiemannVonMangoldtConstantDecayRawFormulaResidual
    (publishedCounting := publishedCounting)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHOn_univ

/--
A fixed-error published `N(T)` source plus constant-decay raw formula-residual
data proves the project RH statement.
-/
theorem RHStatement_of_fixedErrorRiemannVonMangoldt_constantDecay_rawFormulaResidual :
    RiemannHypothesisProject.RHStatement :=
  (eventualPSeriesInputDataOfFixedErrorRiemannVonMangoldtConstantDecayRawFormulaResidual
    (publishedCounting := publishedCounting)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHStatement

/--
A fixed-error published `N(T)` source plus constant-decay raw formula-residual
data proves Mathlib's `RiemannHypothesis`.
-/
theorem mathlib_RH_of_fixedErrorRiemannVonMangoldt_constantDecay_rawFormulaResidual :
    RiemannHypothesis :=
  (eventualPSeriesInputDataOfFixedErrorRiemannVonMangoldtConstantDecayRawFormulaResidual
    (publishedCounting := publishedCounting)
    (growthBound := growthBound)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).mathlib_RH

end FixedErrorRiemannVonMangoldtConstantDecay

end RiemannHypothesisProject
