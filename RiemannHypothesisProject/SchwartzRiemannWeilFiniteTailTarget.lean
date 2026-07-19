import RiemannHypothesisProject.SchwartzRiemannWeilPSeriesEnvelopeTarget

namespace RiemannHypothesisProject

/-!
# Finite-tail eventual p-series targets

This module records the restricted case where the extension envelope is already
zero after a finite cutoff.  In that situation the eventual p-series tail can be
chosen to be the zero p-series, while the finitely many prefix shells are still
bounded explicitly.
-/

/--
Build eventual p-series zero data when the envelope contribution vanishes after
the cutoff.  This is a finite-tail special case of the arbitrary-cutoff p-series
target.
-/
noncomputable def eventuallyZeroEnvelopeZeroData
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_zeroArgument_le_prefix :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        ¬ cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            prefixBound f (exhaustion.zetaZeroFirstEntryIndex rho))
    (tail_envelope_zeroArgument_nonpos :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            0)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData where
  exhaustion := exhaustion
  system := system
  growthBound := growthBound
  cutoff := cutoff
  prefixBound := prefixBound
  zeroConstant := fun _f => 0
  decayExponent := decayExponent
  zeroConstant_nonneg := fun _f => by simp
  prefixBound_nonneg := prefixBound_nonneg
  pseriesBound_nonneg := fun _f _n => by simp
  envelope_zeroArgument_le_eventualPSeries := fun f rho => by
    by_cases hcut : cutoff <= exhaustion.zetaZeroFirstEntryIndex rho
    · simpa [
        SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound,
        hcut
      ] using tail_envelope_zeroArgument_nonpos f rho hcut
    · simpa [
        SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound,
        hcut
      ] using envelope_zeroArgument_le_prefix f rho hcut
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
Build the full eventual p-series endpoint from an eventually-zero envelope,
polynomial zero counting, raw formula sides, and raw residual positivity.
-/
noncomputable def formulaResidualInputDataOfEventuallyZeroEnvelopeAndCountingRaw
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_zeroArgument_le_prefix :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        ¬ cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            prefixBound f (exhaustion.zetaZeroFirstEntryIndex rho))
    (tail_envelope_zeroArgument_nonpos :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            0)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (eventuallyZeroEnvelopeZeroData growthBound cutoff prefixBound
            decayExponent prefixBound_nonneg envelope_zeroArgument_le_prefix
            tail_envelope_zeroArgument_nonpos counting counting_cutoff_eq
            growth_add_one_lt_decay).zeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData := by
  let zeroData :=
    eventuallyZeroEnvelopeZeroData growthBound cutoff prefixBound decayExponent
      prefixBound_nonneg envelope_zeroArgument_le_prefix
      tail_envelope_zeroArgument_nonpos counting counting_cutoff_eq
      growth_add_one_lt_decay
  let formulaData :
      SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaData zeroData :=
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaData.ofRawSides
      primeSide poleSide gammaSide explicitFormula
  let positivityData :
      SchwartzRiemannWeilEventualPSeriesEnvelopeResidualPositivityData
        formulaData :=
    { formulaResidualData :=
        { residual_nonneg := fun f => by
            change 0 <= primeSide f + poleSide f + gammaSide f
            exact residual_nonneg f
          residual_positivity_implies_RHOn_univ := fun hres =>
            residual_positivity_implies_RHOn_univ <| fun f => by
              have hf := hres f
              change 0 <= primeSide f + poleSide f + gammaSide f at hf
              exact hf } }
  exact
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData.ofWorkPackages
      positivityData

/-- The eventually-zero envelope route proves universal local RH. -/
theorem RHOn_univ_of_eventuallyZeroEnvelopeAndCounting_rawFormulaResidual
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_zeroArgument_le_prefix :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        ¬ cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            prefixBound f (exhaustion.zetaZeroFirstEntryIndex rho))
    (tail_envelope_zeroArgument_nonpos :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            0)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (eventuallyZeroEnvelopeZeroData growthBound cutoff prefixBound
            decayExponent prefixBound_nonneg envelope_zeroArgument_le_prefix
            tail_envelope_zeroArgument_nonpos counting counting_cutoff_eq
            growth_add_one_lt_decay).zeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    RHOn (fun _ : Complex => True) :=
  (formulaResidualInputDataOfEventuallyZeroEnvelopeAndCountingRaw
    growthBound cutoff prefixBound decayExponent prefixBound_nonneg
    envelope_zeroArgument_le_prefix tail_envelope_zeroArgument_nonpos
    counting counting_cutoff_eq growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ).RHOn_univ

/-- The eventually-zero envelope route proves the project RH statement. -/
theorem RHStatement_of_eventuallyZeroEnvelopeAndCounting_rawFormulaResidual
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_zeroArgument_le_prefix :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        ¬ cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            prefixBound f (exhaustion.zetaZeroFirstEntryIndex rho))
    (tail_envelope_zeroArgument_nonpos :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            0)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (eventuallyZeroEnvelopeZeroData growthBound cutoff prefixBound
            decayExponent prefixBound_nonneg envelope_zeroArgument_le_prefix
            tail_envelope_zeroArgument_nonpos counting counting_cutoff_eq
            growth_add_one_lt_decay).zeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    RiemannHypothesisProject.RHStatement :=
  (formulaResidualInputDataOfEventuallyZeroEnvelopeAndCountingRaw
    growthBound cutoff prefixBound decayExponent prefixBound_nonneg
    envelope_zeroArgument_le_prefix tail_envelope_zeroArgument_nonpos
    counting counting_cutoff_eq growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ).RHStatement

/-- The eventually-zero envelope route proves Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH_of_eventuallyZeroEnvelopeAndCounting_rawFormulaResidual
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_zeroArgument_le_prefix :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        ¬ cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            prefixBound f (exhaustion.zetaZeroFirstEntryIndex rho))
    (tail_envelope_zeroArgument_nonpos :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        cutoff <= exhaustion.zetaZeroFirstEntryIndex rho ->
          growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
            0)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (eventuallyZeroEnvelopeZeroData growthBound cutoff prefixBound
            decayExponent prefixBound_nonneg envelope_zeroArgument_le_prefix
            tail_envelope_zeroArgument_nonpos counting counting_cutoff_eq
            growth_add_one_lt_decay).zeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    RiemannHypothesis :=
  (formulaResidualInputDataOfEventuallyZeroEnvelopeAndCountingRaw
    growthBound cutoff prefixBound decayExponent prefixBound_nonneg
    envelope_zeroArgument_le_prefix tail_envelope_zeroArgument_nonpos
    counting counting_cutoff_eq growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ).mathlib_RH

end RiemannHypothesisProject
