import RiemannHypothesisProject.SchwartzRiemannWeilPSeriesConstantDecay

/-!
# Reduced conditional Riemann-Weil RH theorems

This file exposes the lower-friction p-series route after the automatic and
constant-decay helpers have removed redundant fields. The remaining hypotheses
are still the genuine analytic inputs: packaged zero counting, a constant-decay
envelope bound, the explicit formula, residual nonnegativity, and the final
residual-positivity-to-RH implication.
-/

namespace RiemannHypothesisProject

section CountingConstantDecay

variable {exhaustion : ComplexCompactExhaustion}
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
variable (zeroConstant : SchwartzLineTestFunction -> Real)
variable (decayExponent : Real)
variable (zeroConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
variable (envelope_zeroArgument_le_pseries :
  forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
    growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      zeroConstant f *
        (1 /
          |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
            decayExponent))
variable (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
variable (counting_cutoff_eq_zero : counting.cutoff = 0)
variable (growth_add_one_lt_decay :
  counting.growth + 1 < decayExponent)
variable (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
variable (explicitFormula :
  forall f : SchwartzLineTestFunction,
    (SchwartzRiemannWeilPSeriesEnvelopeZeroData.ofCountingAndGlobalPSeriesEnvelopeBoundConstantDecay
        growthBound zeroConstant decayExponent zeroConstant_nonneg
        envelope_zeroArgument_le_pseries counting counting_cutoff_eq_zero
        growth_add_one_lt_decay).zeroSide.zeroSide f =
      primeSide f + poleSide f + gammaSide f)
variable (residual_nonneg :
  forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f)
variable (residual_positivity_implies_RHOn_univ :
  (forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f) ->
    RHOn (fun _ : Complex => True))

include growthBound zeroConstant decayExponent zeroConstant_nonneg
  envelope_zeroArgument_le_pseries counting counting_cutoff_eq_zero
  growth_add_one_lt_decay primeSide poleSide gammaSide explicitFormula
  residual_nonneg residual_positivity_implies_RHOn_univ

/--
Assemble packaged cutoff-zero counting and a constant-decay envelope into the
compact p-series formula-residual endpoint.
-/
noncomputable def pSeriesInputDataOfCountingConstantDecayRawFormulaResidual :
    SchwartzRiemannWeilPSeriesEnvelopeFormulaResidualInputData :=
  SchwartzRiemannWeilPSeriesEnvelopeFormulaResidualInputData.ofCountingAndRawFormulaResidualConstantDecay
    growthBound zeroConstant decayExponent zeroConstant_nonneg
    envelope_zeroArgument_le_pseries counting counting_cutoff_eq_zero
    growth_add_one_lt_decay primeSide poleSide gammaSide explicitFormula
    residual_nonneg residual_positivity_implies_RHOn_univ

/--
Packaged cutoff-zero counting plus a constant-decay raw formula-residual package
proves universal local RH.
-/
theorem RHOn_univ_of_counting_constantDecay_rawFormulaResidual :
    RHOn (fun _ : Complex => True) :=
  (pSeriesInputDataOfCountingConstantDecayRawFormulaResidual
    (growthBound := growthBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (envelope_zeroArgument_le_pseries := envelope_zeroArgument_le_pseries)
    (counting := counting)
    (counting_cutoff_eq_zero := counting_cutoff_eq_zero)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHOn_univ

/--
Packaged cutoff-zero counting plus a constant-decay raw formula-residual package
proves the project RH statement.
-/
theorem RHStatement_of_counting_constantDecay_rawFormulaResidual :
    RiemannHypothesisProject.RHStatement :=
  (pSeriesInputDataOfCountingConstantDecayRawFormulaResidual
    (growthBound := growthBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (envelope_zeroArgument_le_pseries := envelope_zeroArgument_le_pseries)
    (counting := counting)
    (counting_cutoff_eq_zero := counting_cutoff_eq_zero)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHStatement

/--
Packaged cutoff-zero counting plus a constant-decay raw formula-residual package
proves Mathlib's `RiemannHypothesis`.
-/
theorem mathlib_RH_of_counting_constantDecay_rawFormulaResidual :
    RiemannHypothesis :=
  (pSeriesInputDataOfCountingConstantDecayRawFormulaResidual
    (growthBound := growthBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (envelope_zeroArgument_le_pseries := envelope_zeroArgument_le_pseries)
    (counting := counting)
    (counting_cutoff_eq_zero := counting_cutoff_eq_zero)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).mathlib_RH

end CountingConstantDecay

section EventualCountingConstantDecay

variable {exhaustion : ComplexCompactExhaustion}
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
variable (cutoff : Nat)
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
        cutoff prefixBound zeroConstant decayExponent f
        (exhaustion.zetaZeroFirstEntryIndex rho))
variable (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
variable (counting_cutoff_eq : counting.cutoff = cutoff)
variable (growth_add_one_lt_decay :
  counting.growth + 1 < decayExponent)
variable (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
variable (explicitFormula :
  forall f : SchwartzLineTestFunction,
    (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofCountingAndEventualPSeriesEnvelopeBoundConstantDecay
        growthBound cutoff prefixBound zeroConstant decayExponent
        zeroConstant_nonneg prefixBound_nonneg
        envelope_zeroArgument_le_eventualConstantPSeries counting
        counting_cutoff_eq growth_add_one_lt_decay).zeroSide.zeroSide f =
      primeSide f + poleSide f + gammaSide f)
variable (residual_nonneg :
  forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f)
variable (residual_positivity_implies_RHOn_univ :
  (forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f) ->
    RHOn (fun _ : Complex => True))

include growthBound cutoff prefixBound zeroConstant decayExponent
  zeroConstant_nonneg prefixBound_nonneg
  envelope_zeroArgument_le_eventualConstantPSeries counting
  counting_cutoff_eq growth_add_one_lt_decay primeSide poleSide gammaSide
  explicitFormula residual_nonneg residual_positivity_implies_RHOn_univ

/--
Assemble packaged eventual counting and a constant-decay envelope into the
compact eventual p-series formula-residual endpoint.
-/
noncomputable def eventualPSeriesInputDataOfCountingConstantDecayRawFormulaResidual :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData.ofCountingAndRawFormulaResidualConstantDecay
    growthBound cutoff prefixBound zeroConstant decayExponent
    zeroConstant_nonneg prefixBound_nonneg
    envelope_zeroArgument_le_eventualConstantPSeries counting
    counting_cutoff_eq growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

/--
Packaged eventual counting plus a constant-decay raw formula-residual package
proves universal local RH.
-/
theorem RHOn_univ_of_eventualCounting_constantDecay_rawFormulaResidual :
    RHOn (fun _ : Complex => True) :=
  (eventualPSeriesInputDataOfCountingConstantDecayRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (counting := counting)
    (counting_cutoff_eq := counting_cutoff_eq)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHOn_univ

/--
Packaged eventual counting plus a constant-decay raw formula-residual package
proves the project RH statement.
-/
theorem RHStatement_of_eventualCounting_constantDecay_rawFormulaResidual :
    RiemannHypothesisProject.RHStatement :=
  (eventualPSeriesInputDataOfCountingConstantDecayRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (counting := counting)
    (counting_cutoff_eq := counting_cutoff_eq)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHStatement

/--
Packaged eventual counting plus a constant-decay raw formula-residual package
proves Mathlib's `RiemannHypothesis`.
-/
theorem mathlib_RH_of_eventualCounting_constantDecay_rawFormulaResidual :
    RiemannHypothesis :=
  (eventualPSeriesInputDataOfCountingConstantDecayRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (envelope_zeroArgument_le_eventualConstantPSeries :=
      envelope_zeroArgument_le_eventualConstantPSeries)
    (counting := counting)
    (counting_cutoff_eq := counting_cutoff_eq)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).mathlib_RH

end EventualCountingConstantDecay

end RiemannHypothesisProject
