import RiemannHypothesisProject.SchwartzRiemannWeilPSeriesEnvelopeTarget

namespace RiemannHypothesisProject

/-!
# Conditional Riemann-Weil RH theorems

This file packages the current best eventual p-series route as theorem-facing
entry points.  The statements deliberately expose the analytic work packages:
zero-counting, eventual p-series decay, the raw explicit formula, residual
nonnegativity, and the final residual-positivity-to-RH implication.
-/

section ExactShellCard

variable {exhaustion : ComplexCompactExhaustion}
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
variable (cutoff : Nat)
variable (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
variable (zeroConstant decayExponent : SchwartzLineTestFunction -> Real)
variable (shellCardConstant growth : Real)
variable (zeroConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
variable (prefixBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
variable (pseriesBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat),
    0 <= zeroConstant f *
      (1 / |(n : Real) + 1| ^ decayExponent f))
variable (shellCardConstant_nonneg : 0 <= shellCardConstant)
variable (tail_shellCard_le :
  forall n : Nat,
    ((exhaustion.zetaZeroFirstEntryShell (n + cutoff)).card : Real) <=
      shellCardConstant * |(n : Real) + 1| ^ growth)
variable (envelope_zeroArgument_le_eventualPSeries :
  forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
    growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound
        cutoff prefixBound zeroConstant decayExponent f
        (exhaustion.zetaZeroFirstEntryIndex rho))
variable (growth_add_one_lt_decay :
  forall f : SchwartzLineTestFunction, growth + 1 < decayExponent f)
variable (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
variable (explicitFormula :
  forall f : SchwartzLineTestFunction,
    (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofExactShellCardAndEventualPSeriesEnvelopeBound
        growthBound cutoff prefixBound zeroConstant decayExponent
        shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
        pseriesBound_nonneg shellCardConstant_nonneg tail_shellCard_le
        envelope_zeroArgument_le_eventualPSeries
        growth_add_one_lt_decay).zeroSide.zeroSide f =
      primeSide f + poleSide f + gammaSide f)
variable (residual_nonneg :
  forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f)
variable (residual_positivity_implies_RHOn_univ :
  (forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f) ->
    RHOn (fun _ : Complex => True))

include growthBound cutoff prefixBound zeroConstant decayExponent
  shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
  pseriesBound_nonneg shellCardConstant_nonneg tail_shellCard_le
  envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
  primeSide poleSide gammaSide explicitFormula residual_nonneg
  residual_positivity_implies_RHOn_univ

/--
Assemble the exact polynomial shell-counting obligations into the eventual
p-series formula-residual endpoint.
-/
noncomputable def eventualPSeriesInputDataOfExactShellCardRawFormulaResidual :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData.ofExactShellCardAndRawFormulaResidual
    growthBound cutoff prefixBound zeroConstant decayExponent
    shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
    pseriesBound_nonneg shellCardConstant_nonneg tail_shellCard_le
    envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

/-- Exact polynomial shell-counting plus the raw formula-residual package proves universal local RH. -/
theorem RHOn_univ_of_exactShellCard_rawFormulaResidual :
    RHOn (fun _ : Complex => True) :=
  (eventualPSeriesInputDataOfExactShellCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (growth := growth)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_shellCard_le := tail_shellCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHOn_univ

/-- Exact polynomial shell-counting plus the raw formula-residual package proves the project RH statement. -/
theorem RHStatement_of_exactShellCard_rawFormulaResidual :
    RiemannHypothesisProject.RHStatement :=
  (eventualPSeriesInputDataOfExactShellCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (growth := growth)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_shellCard_le := tail_shellCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHStatement

/-- Exact polynomial shell-counting plus the raw formula-residual package proves Mathlib RH. -/
theorem mathlib_RH_of_exactShellCard_rawFormulaResidual :
    RiemannHypothesis :=
  (eventualPSeriesInputDataOfExactShellCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (growth := growth)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_shellCard_le := tail_shellCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).mathlib_RH

end ExactShellCard

section UniformTailShellCard

variable {exhaustion : ComplexCompactExhaustion}
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
variable (cutoff : Nat)
variable (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
variable (zeroConstant decayExponent : SchwartzLineTestFunction -> Real)
variable (shellCardConstant : Real)
variable (zeroConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
variable (prefixBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
variable (pseriesBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat),
    0 <= zeroConstant f *
      (1 / |(n : Real) + 1| ^ decayExponent f))
variable (shellCardConstant_nonneg : 0 <= shellCardConstant)
variable (tail_shellCard_le :
  forall n : Nat,
    ((exhaustion.zetaZeroFirstEntryShell (n + cutoff)).card : Real) <=
      shellCardConstant)
variable (envelope_zeroArgument_le_eventualPSeries :
  forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
    growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound
        cutoff prefixBound zeroConstant decayExponent f
        (exhaustion.zetaZeroFirstEntryIndex rho))
variable (growth_add_one_lt_decay :
  forall f : SchwartzLineTestFunction, (0 : Real) + 1 < decayExponent f)
variable (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
variable (explicitFormula :
  forall f : SchwartzLineTestFunction,
    (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofUniformTailShellCardAndEventualPSeriesEnvelopeBound
        growthBound cutoff prefixBound zeroConstant decayExponent
        shellCardConstant zeroConstant_nonneg prefixBound_nonneg
        pseriesBound_nonneg shellCardConstant_nonneg tail_shellCard_le
        envelope_zeroArgument_le_eventualPSeries
        growth_add_one_lt_decay).zeroSide.zeroSide f =
      primeSide f + poleSide f + gammaSide f)
variable (residual_nonneg :
  forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f)
variable (residual_positivity_implies_RHOn_univ :
  (forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f) ->
    RHOn (fun _ : Complex => True))

include growthBound cutoff prefixBound zeroConstant decayExponent
  shellCardConstant zeroConstant_nonneg prefixBound_nonneg pseriesBound_nonneg
  shellCardConstant_nonneg tail_shellCard_le
  envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
  primeSide poleSide gammaSide explicitFormula residual_nonneg
  residual_positivity_implies_RHOn_univ

/--
Assemble the uniform tail shell-counting obligations into the eventual p-series
formula-residual endpoint.
-/
noncomputable def eventualPSeriesInputDataOfUniformTailShellCardRawFormulaResidual :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData.ofUniformTailShellCardAndRawFormulaResidual
    growthBound cutoff prefixBound zeroConstant decayExponent
    shellCardConstant zeroConstant_nonneg prefixBound_nonneg
    pseriesBound_nonneg shellCardConstant_nonneg tail_shellCard_le
    envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

/-- Uniform tail shell-counting plus the raw formula-residual package proves universal local RH. -/
theorem RHOn_univ_of_uniformTailShellCard_rawFormulaResidual :
    RHOn (fun _ : Complex => True) :=
  (eventualPSeriesInputDataOfUniformTailShellCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_shellCard_le := tail_shellCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHOn_univ

/-- Uniform tail shell-counting plus the raw formula-residual package proves the project RH statement. -/
theorem RHStatement_of_uniformTailShellCard_rawFormulaResidual :
    RiemannHypothesisProject.RHStatement :=
  (eventualPSeriesInputDataOfUniformTailShellCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_shellCard_le := tail_shellCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHStatement

/-- Uniform tail shell-counting plus the raw formula-residual package proves Mathlib RH. -/
theorem mathlib_RH_of_uniformTailShellCard_rawFormulaResidual :
    RiemannHypothesis :=
  (eventualPSeriesInputDataOfUniformTailShellCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_shellCard_le := tail_shellCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).mathlib_RH

end UniformTailShellCard

section WindowCard

variable {exhaustion : ComplexCompactExhaustion}
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
variable (cutoff : Nat)
variable (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
variable (zeroConstant decayExponent : SchwartzLineTestFunction -> Real)
variable (shellCardConstant growth : Real)
variable (zeroConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
variable (prefixBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
variable (pseriesBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat),
    0 <= zeroConstant f *
      (1 / |(n : Real) + 1| ^ decayExponent f))
variable (shellCardConstant_nonneg : 0 <= shellCardConstant)
variable (tail_windowCard_le :
  forall n : Nat,
    ((exhaustion.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
      shellCardConstant * |(n : Real) + 1| ^ growth)
variable (envelope_zeroArgument_le_eventualPSeries :
  forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
    growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound
        cutoff prefixBound zeroConstant decayExponent f
        (exhaustion.zetaZeroFirstEntryIndex rho))
variable (growth_add_one_lt_decay :
  forall f : SchwartzLineTestFunction, growth + 1 < decayExponent f)
variable (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
variable (explicitFormula :
  forall f : SchwartzLineTestFunction,
    (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofWindowCardAndEventualPSeriesEnvelopeBound
        growthBound cutoff prefixBound zeroConstant decayExponent
        shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
        pseriesBound_nonneg shellCardConstant_nonneg tail_windowCard_le
        envelope_zeroArgument_le_eventualPSeries
        growth_add_one_lt_decay).zeroSide.zeroSide f =
      primeSide f + poleSide f + gammaSide f)
variable (residual_nonneg :
  forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f)
variable (residual_positivity_implies_RHOn_univ :
  (forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f) ->
    RHOn (fun _ : Complex => True))

include growthBound cutoff prefixBound zeroConstant decayExponent
  shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
  pseriesBound_nonneg shellCardConstant_nonneg tail_windowCard_le
  envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
  primeSide poleSide gammaSide explicitFormula residual_nonneg
  residual_positivity_implies_RHOn_univ

/--
Assemble polynomial cumulative-window zero counting into the eventual p-series
formula-residual endpoint.
-/
noncomputable def eventualPSeriesInputDataOfWindowCardRawFormulaResidual :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData.ofWindowCardAndRawFormulaResidual
    growthBound cutoff prefixBound zeroConstant decayExponent
    shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
    pseriesBound_nonneg shellCardConstant_nonneg tail_windowCard_le
    envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

/-- Polynomial cumulative-window counting plus the raw formula-residual package proves universal local RH. -/
theorem RHOn_univ_of_windowCard_rawFormulaResidual :
    RHOn (fun _ : Complex => True) :=
  (eventualPSeriesInputDataOfWindowCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (growth := growth)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_windowCard_le := tail_windowCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHOn_univ

/-- Polynomial cumulative-window counting plus the raw formula-residual package proves the project RH statement. -/
theorem RHStatement_of_windowCard_rawFormulaResidual :
    RiemannHypothesisProject.RHStatement :=
  (eventualPSeriesInputDataOfWindowCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (growth := growth)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_windowCard_le := tail_windowCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHStatement

/-- Polynomial cumulative-window counting plus the raw formula-residual package proves Mathlib RH. -/
theorem mathlib_RH_of_windowCard_rawFormulaResidual :
    RiemannHypothesis :=
  (eventualPSeriesInputDataOfWindowCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (growth := growth)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_windowCard_le := tail_windowCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).mathlib_RH

end WindowCard

section UniformTailWindowCard

variable {exhaustion : ComplexCompactExhaustion}
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
variable (cutoff : Nat)
variable (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
variable (zeroConstant decayExponent : SchwartzLineTestFunction -> Real)
variable (shellCardConstant : Real)
variable (zeroConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
variable (prefixBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
variable (pseriesBound_nonneg :
  forall (f : SchwartzLineTestFunction) (n : Nat),
    0 <= zeroConstant f *
      (1 / |(n : Real) + 1| ^ decayExponent f))
variable (shellCardConstant_nonneg : 0 <= shellCardConstant)
variable (tail_windowCard_le :
  forall n : Nat,
    ((exhaustion.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
      shellCardConstant)
variable (envelope_zeroArgument_le_eventualPSeries :
  forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
    growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound
        cutoff prefixBound zeroConstant decayExponent f
        (exhaustion.zetaZeroFirstEntryIndex rho))
variable (growth_add_one_lt_decay :
  forall f : SchwartzLineTestFunction, (0 : Real) + 1 < decayExponent f)
variable (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
variable (explicitFormula :
  forall f : SchwartzLineTestFunction,
    (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofUniformTailWindowCardAndEventualPSeriesEnvelopeBound
        growthBound cutoff prefixBound zeroConstant decayExponent
        shellCardConstant zeroConstant_nonneg prefixBound_nonneg
        pseriesBound_nonneg shellCardConstant_nonneg tail_windowCard_le
        envelope_zeroArgument_le_eventualPSeries
        growth_add_one_lt_decay).zeroSide.zeroSide f =
      primeSide f + poleSide f + gammaSide f)
variable (residual_nonneg :
  forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f)
variable (residual_positivity_implies_RHOn_univ :
  (forall f : SchwartzLineTestFunction,
    0 <= primeSide f + poleSide f + gammaSide f) ->
    RHOn (fun _ : Complex => True))

include growthBound cutoff prefixBound zeroConstant decayExponent
  shellCardConstant zeroConstant_nonneg prefixBound_nonneg pseriesBound_nonneg
  shellCardConstant_nonneg tail_windowCard_le
  envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
  primeSide poleSide gammaSide explicitFormula residual_nonneg
  residual_positivity_implies_RHOn_univ

/--
Assemble uniformly bounded cumulative-window zero counting into the eventual
p-series formula-residual endpoint.
-/
noncomputable def eventualPSeriesInputDataOfUniformTailWindowCardRawFormulaResidual :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData.ofUniformTailWindowCardAndRawFormulaResidual
    growthBound cutoff prefixBound zeroConstant decayExponent
    shellCardConstant zeroConstant_nonneg prefixBound_nonneg
    pseriesBound_nonneg shellCardConstant_nonneg tail_windowCard_le
    envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

/-- Uniform cumulative-window counting plus the raw formula-residual package proves universal local RH. -/
theorem RHOn_univ_of_uniformTailWindowCard_rawFormulaResidual :
    RHOn (fun _ : Complex => True) :=
  (eventualPSeriesInputDataOfUniformTailWindowCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_windowCard_le := tail_windowCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHOn_univ

/-- Uniform cumulative-window counting plus the raw formula-residual package proves the project RH statement. -/
theorem RHStatement_of_uniformTailWindowCard_rawFormulaResidual :
    RiemannHypothesisProject.RHStatement :=
  (eventualPSeriesInputDataOfUniformTailWindowCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_windowCard_le := tail_windowCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).RHStatement

/-- Uniform cumulative-window counting plus the raw formula-residual package proves Mathlib RH. -/
theorem mathlib_RH_of_uniformTailWindowCard_rawFormulaResidual :
    RiemannHypothesis :=
  (eventualPSeriesInputDataOfUniformTailWindowCardRawFormulaResidual
    (growthBound := growthBound)
    (cutoff := cutoff)
    (prefixBound := prefixBound)
    (zeroConstant := zeroConstant)
    (decayExponent := decayExponent)
    (shellCardConstant := shellCardConstant)
    (zeroConstant_nonneg := zeroConstant_nonneg)
    (prefixBound_nonneg := prefixBound_nonneg)
    (pseriesBound_nonneg := pseriesBound_nonneg)
    (shellCardConstant_nonneg := shellCardConstant_nonneg)
    (tail_windowCard_le := tail_windowCard_le)
    (envelope_zeroArgument_le_eventualPSeries :=
      envelope_zeroArgument_le_eventualPSeries)
    (growth_add_one_lt_decay := growth_add_one_lt_decay)
    (primeSide := primeSide)
    (poleSide := poleSide)
    (gammaSide := gammaSide)
    (explicitFormula := explicitFormula)
    (residual_nonneg := residual_nonneg)
    (residual_positivity_implies_RHOn_univ :=
      residual_positivity_implies_RHOn_univ)).mathlib_RH

end UniformTailWindowCard

end RiemannHypothesisProject
