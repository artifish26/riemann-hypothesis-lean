import RiemannHypothesisProject.SchwartzRiemannWeilTailEstimates

/-!
# Analytic profiles for Riemann-Weil extension systems

`SchwartzRiemannWeilExtensionSystem` records the bare complex extension data
needed to evaluate a real-line Schwartz test function at the Riemann-Weil zero
argument. This module adds a finer, optional profile layer for the analytic
properties that the eventual explicit formula should require:

* critical-line normalization;
* an abstract symmetry operation;
* a complex envelope bound for the extension; and
* shell-wise decay of that envelope along zeta-zero arguments.

The shell-decay profile converts to the existing
`SchwartzRiemannWeilPolynomialZeroDecayEstimate`, so the tail-estimate and RH
certificate pipeline can use these more structured complex-analytic inputs. The
profile layer is conservative: existing zero-decay estimates can be lifted to a
profile using the exact norm envelope and identity symmetry.
-/

namespace RiemannHypothesisProject

open Filter

/--
Critical-line normalization for an extension system.

The bare extension system already proves this normalization from
`extension_restricts`; packaging it here gives later explicit-formula code a
named field to depend on.
-/
structure SchwartzRiemannWeilExtensionNormalization
    (system : SchwartzRiemannWeilExtensionSystem) where
  zeroValue_criticalLine :
    forall (f : SchwartzLineTestFunction) (t : Real) {rho : ZetaZeroSubtype},
      (rho : Complex) = criticalLinePoint t -> system.zeroValue f rho = f t
  weight_criticalLine :
    forall (f : SchwartzLineTestFunction) (t : Real) {rho : ZetaZeroSubtype},
      (rho : Complex) = criticalLinePoint t ->
        system.weight f rho = (f t).re

namespace SchwartzRiemannWeilExtensionNormalization

/-- Every bare extension system carries the critical-line normalization. -/
noncomputable def ofSystem
    (system : SchwartzRiemannWeilExtensionSystem) :
    SchwartzRiemannWeilExtensionNormalization system where
  zeroValue_criticalLine := fun f t _rho hrho =>
    system.zeroValue_of_criticalLinePoint f t hrho
  weight_criticalLine := fun f t _rho hrho =>
    system.weight_of_criticalLinePoint f t hrho

end SchwartzRiemannWeilExtensionNormalization

/--
An abstract symmetry profile for an extension system.

This does not choose the final Riemann-Weil symmetry. It records the shape of
such data: a transformation of test functions, a transformation of complex
arguments, and compatibility of the extension with those transformations.
-/
structure SchwartzRiemannWeilExtensionSymmetry
    (system : SchwartzRiemannWeilExtensionSystem) where
  testTransform : SchwartzLineTestFunction -> SchwartzLineTestFunction
  argumentTransform : Complex -> Complex
  extension_symmetry :
    forall (f : SchwartzLineTestFunction) (z : Complex),
      system.extension (testTransform f) z =
        system.extension f (argumentTransform z)

namespace SchwartzRiemannWeilExtensionSymmetry

/-- The identity symmetry, useful as a conservative default profile. -/
noncomputable def identity
    (system : SchwartzRiemannWeilExtensionSystem) :
    SchwartzRiemannWeilExtensionSymmetry system where
  testTransform := fun f => f
  argumentTransform := fun z => z
  extension_symmetry := fun _f _z => rfl

/-- Symmetry compatibility specialized to zeta-zero arguments. -/
theorem zeroValue_symmetry
    {system : SchwartzRiemannWeilExtensionSystem}
    (symmetry : SchwartzRiemannWeilExtensionSymmetry system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    system.zeroValue (symmetry.testTransform f) rho =
      system.extension f
        (symmetry.argumentTransform
          (riemannWeilZeroArgument (rho : Complex))) := by
  unfold SchwartzRiemannWeilExtensionSystem.zeroValue
  exact symmetry.extension_symmetry f (riemannWeilZeroArgument (rho : Complex))

/-- The induced real weight obeys the same abstract symmetry after taking real parts. -/
theorem weight_symmetry
    {system : SchwartzRiemannWeilExtensionSystem}
    (symmetry : SchwartzRiemannWeilExtensionSymmetry system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    system.weight (symmetry.testTransform f) rho =
      (system.extension f
        (symmetry.argumentTransform
          (riemannWeilZeroArgument (rho : Complex)))).re := by
  unfold SchwartzRiemannWeilExtensionSystem.weight
  rw [symmetry.zeroValue_symmetry f rho]

end SchwartzRiemannWeilExtensionSymmetry

/--
A complex envelope bound for an extension system.

The envelope is real-valued and nonnegative. It bounds the norm of the complex
extension at every complex argument.
-/
structure SchwartzRiemannWeilExtensionGrowthBound
    (system : SchwartzRiemannWeilExtensionSystem) where
  envelope : SchwartzLineTestFunction -> Complex -> Real
  envelope_nonneg :
    forall (f : SchwartzLineTestFunction) (z : Complex), 0 <= envelope f z
  norm_extension_le :
    forall (f : SchwartzLineTestFunction) (z : Complex),
      norm (system.extension f z) <= envelope f z

namespace SchwartzRiemannWeilExtensionGrowthBound

/-- The exact norm envelope for an extension system. -/
noncomputable def exactNorm
    (system : SchwartzRiemannWeilExtensionSystem) :
    SchwartzRiemannWeilExtensionGrowthBound system where
  envelope := fun f z => norm (system.extension f z)
  envelope_nonneg := fun f z => norm_nonneg (system.extension f z)
  norm_extension_le := fun _f _z => le_rfl

/-- The envelope bounds the norm of the zero contribution. -/
theorem norm_zeroValue_le_envelope
    {system : SchwartzRiemannWeilExtensionSystem}
    (growth : SchwartzRiemannWeilExtensionGrowthBound system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.zeroValue f rho) <=
      growth.envelope f (riemannWeilZeroArgument (rho : Complex)) := by
  unfold SchwartzRiemannWeilExtensionSystem.zeroValue
  exact growth.norm_extension_le f (riemannWeilZeroArgument (rho : Complex))

end SchwartzRiemannWeilExtensionGrowthBound

/--
Shell-wise decay of an extension envelope along zeta-zero arguments.

This is the complex-analysis-facing version of the zero-decay estimate used by
the tail pipeline. It starts with a global envelope bound for the extension,
then bounds that envelope on each first-entry shell of a compact exhaustion.
-/
structure SchwartzRiemannWeilExtensionShellDecayEstimate
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  growthBound : SchwartzRiemannWeilExtensionGrowthBound system
  cutoff : Nat
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  zeroConstant : SchwartzLineTestFunction -> Real
  decayExponent : SchwartzLineTestFunction -> Real
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  envelope_zeroArgument_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <=
        zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f)

namespace SchwartzRiemannWeilExtensionShellDecayEstimate

/-- An envelope p-series term is nonnegative when its leading constant is. -/
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

/--
The shell bound used for eventual p-series envelope estimates: before `cutoff`
it uses an explicit prefix bound, and from `cutoff` onward it uses the shifted
p-series tail indexed from zero.
-/
noncomputable def eventualPSeriesShellBound
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (n : Nat) : Real :=
  if cutoff ≤ n then
    zeroConstant f *
      (1 / |((n - cutoff : Nat) : Real) + 1| ^ decayExponent f)
  else
    prefixBound f n

/--
Build shell-decay data from a direct global p-series bound on the extension
envelope at each zero argument's first-entry shell index. This is the
cutoff-zero case.
-/
noncomputable def ofGlobalPSeriesEnvelopeBound
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (pseriesBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= zeroConstant f *
          (1 / |(n : Real) + 1| ^ decayExponent f))
    (envelope_zeroArgument_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f)) :
    SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system where
  growthBound := growthBound
  cutoff := 0
  shellBound := fun f n =>
    zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f)
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  zeroConstant_nonneg := zeroConstant_nonneg
  shellBound_nonneg := pseriesBound_nonneg
  envelope_zeroArgument_le_shellBound := envelope_zeroArgument_le_pseries
  tail_shellBound_le := fun _f _n => le_rfl

/--
Build shell-decay data from an eventual p-series bound on the extension
envelope. The finite prefix is bounded separately by `prefixBound`; after
`cutoff`, the bound is the shifted p-series
`zeroConstant f / |n + 1| ^ decayExponent f`.
-/
noncomputable def ofEventualPSeriesEnvelopeBound
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
    (pseriesBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= zeroConstant f *
          (1 / |(n : Real) + 1| ^ decayExponent f))
    (envelope_zeroArgument_le_eventualPSeries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          eventualPSeriesShellBound cutoff prefixBound zeroConstant
            decayExponent f (exhaustion.zetaZeroFirstEntryIndex rho)) :
    SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system where
  growthBound := growthBound
  cutoff := cutoff
  shellBound :=
    eventualPSeriesShellBound cutoff prefixBound zeroConstant decayExponent
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  zeroConstant_nonneg := zeroConstant_nonneg
  shellBound_nonneg := fun f n => by
    unfold eventualPSeriesShellBound
    by_cases hcut : cutoff ≤ n
    · simp only [hcut, if_true]
      exact pseriesBound_nonneg f (n - cutoff)
    · simp [hcut, prefixBound_nonneg f n]
  envelope_zeroArgument_le_shellBound :=
    envelope_zeroArgument_le_eventualPSeries
  tail_shellBound_le := fun f n => by
    unfold eventualPSeriesShellBound
    have hcut : cutoff ≤ n + cutoff := Nat.le_add_left cutoff n
    have hsub : (n + cutoff) - cutoff = n := Nat.add_sub_cancel_right n cutoff
    simp [hcut, hsub]

/--
Build shell-decay data from a direct global p-series envelope bound, deriving
p-series nonnegativity from `zeroConstant_nonneg`.
-/
noncomputable def ofGlobalPSeriesEnvelopeBoundOfNonnegConstant
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
                decayExponent f)) :
    SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system :=
  ofGlobalPSeriesEnvelopeBound growthBound zeroConstant decayExponent
    zeroConstant_nonneg
    (fun f n => pseriesEnvelopeTerm_nonneg zeroConstant_nonneg f n)
    envelope_zeroArgument_le_pseries

/--
Any polynomial zero-decay estimate can be viewed as shell decay of the exact
norm envelope.
-/
noncomputable def ofPolynomialZeroDecayEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (decay :
      SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system) :
    SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system where
  growthBound := SchwartzRiemannWeilExtensionGrowthBound.exactNorm system
  cutoff := decay.cutoff
  shellBound := decay.shellBound
  zeroConstant := decay.zeroConstant
  decayExponent := decay.decayExponent
  zeroConstant_nonneg := decay.zeroConstant_nonneg
  shellBound_nonneg := decay.shellBound_nonneg
  envelope_zeroArgument_le_shellBound := fun f rho => by
    simpa [SchwartzRiemannWeilExtensionGrowthBound.exactNorm,
      SchwartzRiemannWeilExtensionSystem.zeroValue]
      using decay.norm_zeroValue_le_shellBound f rho
  tail_shellBound_le := decay.tail_shellBound_le

/--
Extension envelope decay produces the zero-decay estimate consumed by the tail
pipeline.
-/
noncomputable def toPolynomialZeroDecayEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (decay :
      SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system) :
    SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system where
  cutoff := decay.cutoff
  shellBound := decay.shellBound
  zeroConstant := decay.zeroConstant
  decayExponent := decay.decayExponent
  zeroConstant_nonneg := decay.zeroConstant_nonneg
  shellBound_nonneg := decay.shellBound_nonneg
  tail_shellBound_le := decay.tail_shellBound_le
  norm_zeroValue_le_shellBound := fun f rho =>
    le_trans (decay.growthBound.norm_zeroValue_le_envelope f rho)
      (decay.envelope_zeroArgument_le_shellBound f rho)

end SchwartzRiemannWeilExtensionShellDecayEstimate

/--
A named analytic profile for an extension system relative to a compact
exhaustion.

The profile combines normalization, symmetry, and envelope decay. The
normalization component can always be supplied by `ofSystem`; the symmetry and
decay components are the substantive future analytic work.
-/
structure SchwartzRiemannWeilExtensionAnalyticProfile
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  normalization : SchwartzRiemannWeilExtensionNormalization system
  symmetry : SchwartzRiemannWeilExtensionSymmetry system
  shellDecay :
    SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system

namespace SchwartzRiemannWeilExtensionAnalyticProfile

/--
Lift an existing polynomial zero-decay estimate to an analytic extension
profile using the default critical-line normalization, identity symmetry, and
exact norm envelope.
-/
noncomputable def ofPolynomialZeroDecayEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (decay :
      SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system) :
    SchwartzRiemannWeilExtensionAnalyticProfile exhaustion system where
  normalization := SchwartzRiemannWeilExtensionNormalization.ofSystem system
  symmetry := SchwartzRiemannWeilExtensionSymmetry.identity system
  shellDecay :=
    SchwartzRiemannWeilExtensionShellDecayEstimate.ofPolynomialZeroDecayEstimate
      decay

/--
Build an analytic extension profile from shell-decay data using the default
critical-line normalization and identity symmetry.
-/
noncomputable def ofShellDecayEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (shellDecay :
      SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system) :
    SchwartzRiemannWeilExtensionAnalyticProfile exhaustion system where
  normalization := SchwartzRiemannWeilExtensionNormalization.ofSystem system
  symmetry := SchwartzRiemannWeilExtensionSymmetry.identity system
  shellDecay := shellDecay

/-- A profiled extension system supplies the polynomial zero-decay estimate. -/
noncomputable def toPolynomialZeroDecayEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (profile :
      SchwartzRiemannWeilExtensionAnalyticProfile exhaustion system) :
    SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system :=
  profile.shellDecay.toPolynomialZeroDecayEstimate

end SchwartzRiemannWeilExtensionAnalyticProfile

/--
Separated tail estimates whose zero-decay side comes from an analytic extension
profile.
-/
structure SchwartzRiemannWeilProfiledSeparatedTailEstimate
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  profile : SchwartzRiemannWeilExtensionAnalyticProfile exhaustion system
  counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion
  cutoff_eq : counting.cutoff = profile.shellDecay.cutoff
  growth_add_one_lt_decay :
    forall f : SchwartzLineTestFunction,
      counting.growth + 1 < profile.shellDecay.decayExponent f

namespace SchwartzRiemannWeilProfiledSeparatedTailEstimate

/--
Lift an existing separated polynomial tail estimate into the profiled form using
the conservative exact-norm profile.
-/
noncomputable def ofSeparatedPolynomialDecayEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system where
  profile :=
    SchwartzRiemannWeilExtensionAnalyticProfile.ofPolynomialZeroDecayEstimate
      estimate.decay
  counting := estimate.counting
  cutoff_eq := estimate.cutoff_eq
  growth_add_one_lt_decay := estimate.growth_add_one_lt_decay

/--
Build a profiled separated tail estimate from extension shell-decay data and
zero-counting data, using the default normalization and identity symmetry.
-/
noncomputable def ofShellDecayAndCounting
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (shellDecay :
      SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (cutoff_eq : counting.cutoff = shellDecay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < shellDecay.decayExponent f) :
    SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system where
  profile :=
    SchwartzRiemannWeilExtensionAnalyticProfile.ofShellDecayEstimate shellDecay
  counting := counting
  cutoff_eq := cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
A profiled extension plus zero counting produces the separated polynomial tail
estimate.
-/
noncomputable def toSeparatedPolynomialDecayEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system) :
    SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system where
  counting := estimate.counting
  decay := estimate.profile.toPolynomialZeroDecayEstimate
  cutoff_eq := estimate.cutoff_eq
  growth_add_one_lt_decay := estimate.growth_add_one_lt_decay

/-- Profiled separated estimates produce the candidate zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toSeparatedPolynomialDecayEstimate.toZeroSide

/-- The zero side induced by profiled estimates has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  estimate.toSeparatedPolynomialDecayEstimate.toZeroSide_weight f rho

/-- Compact-exhaustion sums for profiled estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toSeparatedPolynomialDecayEstimate.tendsto_windowZeroSide
    windowExhaustion f

end SchwartzRiemannWeilProfiledSeparatedTailEstimate

end RiemannHypothesisProject
