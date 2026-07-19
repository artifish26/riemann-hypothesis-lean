import RiemannHypothesisProject.SchwartzRiemannWeilPSeriesEnvelopeTarget

/-!
# Automatic p-series envelope helpers

The p-series envelope target asks for nonnegativity of

`zeroConstant f * (1 / |n + 1| ^ decayExponent f)`.

That proof is elementary once `zeroConstant` is nonnegative.  This file records
that fact and adds constructors that remove the redundant nonnegativity field
from the most direct p-series envelope entry points.
-/

namespace RiemannHypothesisProject

/-- A p-series envelope term is nonnegative when its leading constant is. -/
theorem pseriesEnvelopeTerm_nonneg
    {zeroConstant decayExponent : SchwartzLineTestFunction -> Real}
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    0 <=
      zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f) :=
  mul_nonneg (zeroConstant_nonneg f)
    (one_div_nonneg.mpr
      (Real.rpow_nonneg (abs_nonneg ((n : Real) + 1))
        (decayExponent f)))

namespace SchwartzRiemannWeilExtensionShellDecayEstimate

/--
Build eventual shell-decay data from an eventual p-series envelope bound,
deriving p-series nonnegativity automatically from `zeroConstant_nonneg`.
-/
noncomputable def ofEventualPSeriesEnvelopeBoundOfNonnegConstant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= prefixBound f n)
    (envelope_zeroArgument_le_eventualPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          eventualPSeriesShellBound cutoff prefixBound zeroConstant
            decayExponent f (exhaustion.zetaZeroFirstEntryIndex rho)) :
    SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system :=
  ofEventualPSeriesEnvelopeBound growthBound cutoff prefixBound zeroConstant
    decayExponent zeroConstant_nonneg prefixBound_nonneg
    (fun f n => pseriesEnvelopeTerm_nonneg zeroConstant_nonneg f n)
    envelope_zeroArgument_le_eventualPSeries

end SchwartzRiemannWeilExtensionShellDecayEstimate

namespace SchwartzRiemannWeilPSeriesEnvelopeZeroData

/--
Build cutoff-zero p-series zero data from a counting estimate and direct
envelope bound, deriving p-series nonnegativity automatically.
-/
noncomputable def ofCountingAndGlobalPSeriesEnvelopeBound
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (envelope_zeroArgument_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f))
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq_zero : counting.cutoff = 0)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f) :
    SchwartzRiemannWeilPSeriesEnvelopeZeroData where
  exhaustion := exhaustion
  system := system
  growthBound := growthBound
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  zeroConstant_nonneg := zeroConstant_nonneg
  pseriesBound_nonneg :=
    fun f n => pseriesEnvelopeTerm_nonneg zeroConstant_nonneg f n
  envelope_zeroArgument_le_pseries := envelope_zeroArgument_le_pseries
  counting := counting
  counting_cutoff_eq_zero := counting_cutoff_eq_zero
  growth_add_one_lt_decay := growth_add_one_lt_decay

end SchwartzRiemannWeilPSeriesEnvelopeZeroData

namespace SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData

/--
Build eventual p-series zero data from a counting estimate and eventual
envelope bound, deriving p-series nonnegativity automatically.
-/
noncomputable def ofCountingAndEventualPSeriesEnvelopeBound
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= prefixBound f n)
    (envelope_zeroArgument_le_eventualPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound
            cutoff prefixBound zeroConstant decayExponent f
            (exhaustion.zetaZeroFirstEntryIndex rho))
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
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  zeroConstant_nonneg := zeroConstant_nonneg
  prefixBound_nonneg := prefixBound_nonneg
  pseriesBound_nonneg :=
    fun f n => pseriesEnvelopeTerm_nonneg zeroConstant_nonneg f n
  envelope_zeroArgument_le_eventualPSeries :=
    envelope_zeroArgument_le_eventualPSeries
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

end SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData

namespace SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData

/--
Build the full eventual p-series endpoint from exact polynomial shell counting,
deriving p-series nonnegativity automatically from `zeroConstant_nonneg`.
-/
noncomputable def ofExactShellCardAndRawFormulaResidualOfNonnegConstant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (shellCardConstant growth : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (shellCardConstant_nonneg : 0 <= shellCardConstant)
    (tail_shellCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroFirstEntryShell (n + cutoff)).card : Real) <=
          shellCardConstant * |(n : Real) + 1| ^ growth)
    (envelope_zeroArgument_le_eventualPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound
            cutoff prefixBound zeroConstant decayExponent f
            (exhaustion.zetaZeroFirstEntryIndex rho))
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction, growth + 1 < decayExponent f)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofExactShellCardAndEventualPSeriesEnvelopeBound
            growthBound cutoff prefixBound zeroConstant decayExponent
            shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
            (fun f n =>
              pseriesEnvelopeTerm_nonneg
                (zeroConstant := zeroConstant)
                (decayExponent := decayExponent)
                zeroConstant_nonneg f n)
            shellCardConstant_nonneg tail_shellCard_le
            envelope_zeroArgument_le_eventualPSeries
            growth_add_one_lt_decay).zeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  ofExactShellCardAndRawFormulaResidual
    growthBound cutoff prefixBound zeroConstant decayExponent
    shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
    (fun f n =>
      pseriesEnvelopeTerm_nonneg
        (zeroConstant := zeroConstant)
        (decayExponent := decayExponent)
        zeroConstant_nonneg f n)
    shellCardConstant_nonneg tail_shellCard_le
    envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

/--
Build the full eventual p-series endpoint from uniformly bounded tail shell
counts, deriving p-series nonnegativity automatically.
-/
noncomputable def ofUniformTailShellCardAndRawFormulaResidualOfNonnegConstant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (shellCardConstant : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (shellCardConstant_nonneg : 0 <= shellCardConstant)
    (tail_shellCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroFirstEntryShell (n + cutoff)).card : Real) <=
          shellCardConstant)
    (envelope_zeroArgument_le_eventualPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound
            cutoff prefixBound zeroConstant decayExponent f
            (exhaustion.zetaZeroFirstEntryIndex rho))
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction, (0 : Real) + 1 < decayExponent f)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofUniformTailShellCardAndEventualPSeriesEnvelopeBound
            growthBound cutoff prefixBound zeroConstant decayExponent
            shellCardConstant zeroConstant_nonneg prefixBound_nonneg
            (fun f n =>
              pseriesEnvelopeTerm_nonneg
                (zeroConstant := zeroConstant)
                (decayExponent := decayExponent)
                zeroConstant_nonneg f n)
            shellCardConstant_nonneg tail_shellCard_le
            envelope_zeroArgument_le_eventualPSeries
            growth_add_one_lt_decay).zeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  ofUniformTailShellCardAndRawFormulaResidual
    growthBound cutoff prefixBound zeroConstant decayExponent shellCardConstant
    zeroConstant_nonneg prefixBound_nonneg
    (fun f n =>
      pseriesEnvelopeTerm_nonneg
        (zeroConstant := zeroConstant)
        (decayExponent := decayExponent)
        zeroConstant_nonneg f n)
    shellCardConstant_nonneg tail_shellCard_le
    envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

/--
Build the full eventual p-series endpoint from polynomial cumulative window
counting, deriving p-series nonnegativity automatically.
-/
noncomputable def ofWindowCardAndRawFormulaResidualOfNonnegConstant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (shellCardConstant growth : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (shellCardConstant_nonneg : 0 <= shellCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
          shellCardConstant * |(n : Real) + 1| ^ growth)
    (envelope_zeroArgument_le_eventualPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound
            cutoff prefixBound zeroConstant decayExponent f
            (exhaustion.zetaZeroFirstEntryIndex rho))
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction, growth + 1 < decayExponent f)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofWindowCardAndEventualPSeriesEnvelopeBound
            growthBound cutoff prefixBound zeroConstant decayExponent
            shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
            (fun f n =>
              pseriesEnvelopeTerm_nonneg
                (zeroConstant := zeroConstant)
                (decayExponent := decayExponent)
                zeroConstant_nonneg f n)
            shellCardConstant_nonneg tail_windowCard_le
            envelope_zeroArgument_le_eventualPSeries
            growth_add_one_lt_decay).zeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  ofWindowCardAndRawFormulaResidual
    growthBound cutoff prefixBound zeroConstant decayExponent
    shellCardConstant growth zeroConstant_nonneg prefixBound_nonneg
    (fun f n =>
      pseriesEnvelopeTerm_nonneg
        (zeroConstant := zeroConstant)
        (decayExponent := decayExponent)
        zeroConstant_nonneg f n)
    shellCardConstant_nonneg tail_windowCard_le
    envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

/--
Build the full eventual p-series endpoint from uniformly bounded cumulative
window counts, deriving p-series nonnegativity automatically.
-/
noncomputable def ofUniformTailWindowCardAndRawFormulaResidualOfNonnegConstant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (shellCardConstant : Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (shellCardConstant_nonneg : 0 <= shellCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
          shellCardConstant)
    (envelope_zeroArgument_le_eventualPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound
            cutoff prefixBound zeroConstant decayExponent f
            (exhaustion.zetaZeroFirstEntryIndex rho))
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction, (0 : Real) + 1 < decayExponent f)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofUniformTailWindowCardAndEventualPSeriesEnvelopeBound
            growthBound cutoff prefixBound zeroConstant decayExponent
            shellCardConstant zeroConstant_nonneg prefixBound_nonneg
            (fun f n =>
              pseriesEnvelopeTerm_nonneg
                (zeroConstant := zeroConstant)
                (decayExponent := decayExponent)
                zeroConstant_nonneg f n)
            shellCardConstant_nonneg tail_windowCard_le
            envelope_zeroArgument_le_eventualPSeries
            growth_add_one_lt_decay).zeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  ofUniformTailWindowCardAndRawFormulaResidual
    growthBound cutoff prefixBound zeroConstant decayExponent shellCardConstant
    zeroConstant_nonneg prefixBound_nonneg
    (fun f n =>
      pseriesEnvelopeTerm_nonneg
        (zeroConstant := zeroConstant)
        (decayExponent := decayExponent)
        zeroConstant_nonneg f n)
    shellCardConstant_nonneg tail_windowCard_le
    envelope_zeroArgument_le_eventualPSeries growth_add_one_lt_decay
    primeSide poleSide gammaSide explicitFormula residual_nonneg
    residual_positivity_implies_RHOn_univ

end SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData

end RiemannHypothesisProject
