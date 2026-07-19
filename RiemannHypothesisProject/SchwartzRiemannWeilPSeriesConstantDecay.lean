import RiemannHypothesisProject.SchwartzRiemannWeilPSeriesEnvelopeAutomatic

/-!
# Constant-decay p-series envelope helpers

Many analytic estimates use one global p-series decay exponent, not an exponent
depending on the test function.  The main p-series envelope APIs keep the more
general function-valued exponent, so this file supplies thin checked wrappers
for the common constant-exponent case.
-/

namespace RiemannHypothesisProject

namespace SchwartzRiemannWeilExtensionShellDecayEstimate

/--
The eventual p-series shell bound with one global decay exponent.

This is definitionally the same as `eventualPSeriesShellBound` with
`decayExponent := fun _ => decayExponent`, but gives future analytic estimates
a cleaner statement shape.
-/
noncomputable def eventualConstantPSeriesShellBound
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (f : SchwartzLineTestFunction)
    (n : Nat) : Real :=
  if cutoff <= n then
    zeroConstant f *
      (1 / |((n - cutoff : Nat) : Real) + 1| ^ decayExponent)
  else
    prefixBound f n

/-- The constant-decay shell bound is the function-valued bound with a constant exponent. -/
theorem eventualPSeriesShellBound_constDecay
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    eventualPSeriesShellBound cutoff prefixBound zeroConstant
        (fun _ : SchwartzLineTestFunction => decayExponent) f n =
      eventualConstantPSeriesShellBound cutoff prefixBound zeroConstant
        decayExponent f n := by
  rfl

/--
Build shell-decay data from an eventual p-series envelope bound with one global
decay exponent, deriving nonnegativity automatically from `zeroConstant_nonneg`.
-/
noncomputable def ofEventualConstantPSeriesEnvelopeBoundOfNonnegConstant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= prefixBound f n)
    (envelope_zeroArgument_le_eventualConstantPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          eventualConstantPSeriesShellBound cutoff prefixBound zeroConstant
            decayExponent f (exhaustion.zetaZeroFirstEntryIndex rho)) :
    SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system :=
  ofEventualPSeriesEnvelopeBoundOfNonnegConstant
    growthBound cutoff prefixBound zeroConstant
    (fun _ : SchwartzLineTestFunction => decayExponent)
    zeroConstant_nonneg prefixBound_nonneg
    (fun f rho => by
      rw [eventualPSeriesShellBound_constDecay]
      exact envelope_zeroArgument_le_eventualConstantPSeries f rho)

end SchwartzRiemannWeilExtensionShellDecayEstimate

/-- A single decay margin implies the test-function-indexed margin. -/
theorem growth_add_one_lt_constant_decay
    (growth decayExponent : Real)
    (hdecay : growth + 1 < decayExponent) :
    forall _f : SchwartzLineTestFunction,
      growth + 1 < (fun _ : SchwartzLineTestFunction => decayExponent) _f :=
  fun _f => hdecay

namespace SchwartzRiemannWeilPSeriesEnvelopeZeroData

/--
Build cutoff-zero p-series zero data using one global decay exponent.
-/
noncomputable def ofCountingAndGlobalPSeriesEnvelopeBoundConstantDecay
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (envelope_zeroArgument_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent))
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq_zero : counting.cutoff = 0)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    SchwartzRiemannWeilPSeriesEnvelopeZeroData :=
  ofCountingAndGlobalPSeriesEnvelopeBound
    growthBound zeroConstant
    (fun _ : SchwartzLineTestFunction => decayExponent)
    zeroConstant_nonneg
    (fun f rho => by
      simpa using envelope_zeroArgument_le_pseries f rho)
    counting counting_cutoff_eq_zero
    (growth_add_one_lt_constant_decay
      counting.growth decayExponent growth_add_one_lt_decay)

end SchwartzRiemannWeilPSeriesEnvelopeZeroData

namespace SchwartzRiemannWeilPSeriesEnvelopeFormulaResidualInputData

/--
Build the cutoff-zero p-series endpoint from packaged counting, a global
constant-decay envelope bound, raw formula sides, and raw residual positivity.
-/
noncomputable def ofCountingAndRawFormulaResidualConstantDecay
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (envelope_zeroArgument_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent))
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq_zero : counting.cutoff = 0)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (SchwartzRiemannWeilPSeriesEnvelopeZeroData.ofCountingAndGlobalPSeriesEnvelopeBoundConstantDecay
            growthBound zeroConstant decayExponent zeroConstant_nonneg
            envelope_zeroArgument_le_pseries counting
            counting_cutoff_eq_zero growth_add_one_lt_decay).zeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilPSeriesEnvelopeFormulaResidualInputData := by
  let zeroData :=
    SchwartzRiemannWeilPSeriesEnvelopeZeroData.ofCountingAndGlobalPSeriesEnvelopeBoundConstantDecay
      growthBound zeroConstant decayExponent zeroConstant_nonneg
      envelope_zeroArgument_le_pseries counting counting_cutoff_eq_zero
      growth_add_one_lt_decay
  let formulaData :
      SchwartzRiemannWeilPSeriesEnvelopeFormulaData zeroData :=
    SchwartzRiemannWeilPSeriesEnvelopeFormulaData.ofRawSides
      primeSide poleSide gammaSide explicitFormula
  let positivityData :
      SchwartzRiemannWeilPSeriesEnvelopeResidualPositivityData formulaData :=
    { formulaResidualData :=
        { residual_nonneg := fun f => by
            change 0 <= primeSide f + poleSide f + gammaSide f
            exact residual_nonneg f
          residual_positivity_implies_RHOn_univ := fun hres =>
            residual_positivity_implies_RHOn_univ <| fun f => by
              have hf := hres f
              change 0 <= primeSide f + poleSide f + gammaSide f at hf
              exact hf } }
  exact ofWorkPackages positivityData

end SchwartzRiemannWeilPSeriesEnvelopeFormulaResidualInputData

namespace SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData

/--
Build eventual p-series zero data using one global decay exponent.
-/
noncomputable def ofCountingAndEventualPSeriesEnvelopeBoundConstantDecay
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= prefixBound f n)
    (envelope_zeroArgument_le_eventualConstantPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
            cutoff prefixBound zeroConstant decayExponent f
            (exhaustion.zetaZeroFirstEntryIndex rho))
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  ofCountingAndEventualPSeriesEnvelopeBound
    growthBound cutoff prefixBound zeroConstant
    (fun _ : SchwartzLineTestFunction => decayExponent)
    zeroConstant_nonneg prefixBound_nonneg
    (fun f rho => by
      rw [SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound_constDecay]
      exact envelope_zeroArgument_le_eventualConstantPSeries f rho)
    counting counting_cutoff_eq
    (growth_add_one_lt_constant_decay
      counting.growth decayExponent growth_add_one_lt_decay)

end SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData

namespace SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData

/--
Build the eventual p-series endpoint from packaged counting, a global
constant-decay envelope bound, raw formula sides, and raw residual positivity.
-/
noncomputable def ofCountingAndRawFormulaResidualConstantDecay
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= prefixBound f n)
    (envelope_zeroArgument_le_eventualConstantPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
            cutoff prefixBound zeroConstant decayExponent f
            (exhaustion.zetaZeroFirstEntryIndex rho))
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofCountingAndEventualPSeriesEnvelopeBoundConstantDecay
            growthBound cutoff prefixBound zeroConstant decayExponent
            zeroConstant_nonneg prefixBound_nonneg
            envelope_zeroArgument_le_eventualConstantPSeries counting
            counting_cutoff_eq growth_add_one_lt_decay).zeroSide.zeroSide f =
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
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofCountingAndEventualPSeriesEnvelopeBoundConstantDecay
      growthBound cutoff prefixBound zeroConstant decayExponent
      zeroConstant_nonneg prefixBound_nonneg
      envelope_zeroArgument_le_eventualConstantPSeries counting
      counting_cutoff_eq growth_add_one_lt_decay
  exact ofZeroDataAndRawFormulaResidual zeroData primeSide poleSide gammaSide
    explicitFormula residual_nonneg residual_positivity_implies_RHOn_univ

end SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData

end RiemannHypothesisProject
