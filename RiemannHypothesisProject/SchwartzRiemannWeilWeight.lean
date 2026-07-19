import Mathlib.Analysis.PSeries
import RiemannHypothesisProject.SchwartzRiemannWeilZeroSide

/-!
# Candidate Schwartz Riemann-Weil zero weight

The abstract zero-side interface only asks for a real-valued summable weight on
actual zeta zeroes. This file records a more faithful target shape for that
weight.

For a zeta zero `rho`, the explicit-formula spectral parameter is

```text
(rho - 1/2) / i.
```

If `rho = 1/2 + i t`, this parameter is the real height `t`. Since a
`SchwartzLineTestFunction` is only defined on the real line, a genuine
Riemann-Weil zero contribution also needs complex evaluation data. We package
that as an extension system and use the real part of the complex zero
contribution as the real-valued weight expected by the existing interfaces.
-/

namespace RiemannHypothesisProject

open Filter

/-- The complex spectral parameter attached to a candidate zeta zero. -/
noncomputable def riemannWeilZeroArgument (rho : Complex) : Complex :=
  (rho - (1 / 2 : Complex)) / Complex.I

/-- On the critical line, the Riemann-Weil zero argument recovers the real height. -/
theorem riemannWeilZeroArgument_criticalLinePoint (t : Real) :
    riemannWeilZeroArgument (criticalLinePoint t) = (t : Complex) := by
  unfold riemannWeilZeroArgument criticalLinePoint
  field_simp [Complex.I_ne_zero]
  ring

/--
Complex evaluation data for the Schwartz Riemann-Weil zero contribution.

The field `extension` assigns to each real-line Schwartz test function a
complex-valued function on `Complex`. The restriction field says this extension
agrees with the original Schwartz function on real points. The differentiability
field is the minimal checked placeholder for the future entire-function
requirement; sharper growth and Paley-Wiener-style hypotheses can be added as
the analytic normalization is made more precise.
-/
structure SchwartzRiemannWeilExtensionSystem where
  extension : SchwartzLineTestFunction -> Complex -> Complex
  extension_restricts :
    forall f : SchwartzLineTestFunction,
      forall t : Real, extension f (t : Complex) = f t
  extension_differentiable :
    forall f : SchwartzLineTestFunction, Differentiable Complex (extension f)

namespace SchwartzRiemannWeilExtensionSystem

/-- The complex zero contribution before projecting to the real-valued normalization. -/
noncomputable def zeroValue
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) : Complex :=
  system.extension f (riemannWeilZeroArgument (rho : Complex))

/-- The real-valued candidate zero weight used by the existing zero-side interface. -/
noncomputable def weight
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) : Real :=
  (system.zeroValue f rho).re

/-- The complex zero value at a critical-line point is the original real-line test value. -/
theorem zeroValue_of_criticalLinePoint
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (t : Real)
    {rho : ZetaZeroSubtype}
    (hrho : (rho : Complex) = criticalLinePoint t) :
    system.zeroValue f rho = f t := by
  unfold zeroValue
  rw [hrho, riemannWeilZeroArgument_criticalLinePoint]
  exact system.extension_restricts f t

/-- At a critical-line point, the real weight is the real part of the test value. -/
theorem weight_of_criticalLinePoint
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (t : Real)
    {rho : ZetaZeroSubtype}
    (hrho : (rho : Complex) = criticalLinePoint t) :
    system.weight f rho = (f t).re := by
  unfold weight
  rw [system.zeroValue_of_criticalLinePoint f t hrho]

/--
Turn a candidate extension system into the existing Riemann-Weil zero-side
interface once summability of the induced real weight has been proved.
-/
noncomputable def toZeroSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f)) :
    SchwartzRiemannWeilZeroSide where
  weight := system.weight
  summable_weight := hsummable

/-- The zero side built from an extension system has exactly the induced weight. -/
theorem toZeroSide_weight
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    (system.toZeroSide hsummable).weight f rho = system.weight f rho :=
  rfl

/-- The real candidate weight is bounded by the complex zero contribution's norm. -/
theorem norm_weight_le_norm_zeroValue
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.weight f rho) <= norm (system.zeroValue f rho) := by
  unfold weight
  simpa [Real.norm_eq_abs] using
    Complex.abs_re_le_norm (system.zeroValue f rho)

/-- If the complex zero contribution vanishes, then the real project weight vanishes. -/
theorem weight_eq_zero_of_zeroValue_eq_zero
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (hzero : system.zeroValue f rho = 0) :
    system.weight f rho = 0 := by
  unfold weight
  rw [hzero]
  simp

/--
If the extension vanishes at a Riemann-Weil zero argument, then the induced raw
project weight vanishes at that zero.
-/
theorem weight_eq_zero_of_zeroArgument_extension_eq_zero
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (hzero :
      system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0) :
    system.weight f rho = 0 := by
  exact system.weight_eq_zero_of_zeroValue_eq_zero f rho hzero

/--
The analytic trivial-zero extension-vanishing normalization implies the raw
trivial-zero project-weight vanishing used by the completed-zeta source formula
transfer.
-/
theorem trivial_weight_eq_zero_of_trivial_zeroArgument_extension_eq_zero
    (system : SchwartzRiemannWeilExtensionSystem)
    (htrivial_extension :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) ->
            system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0) :
    forall f : SchwartzLineTestFunction,
      forall rho : ZetaZeroSubtype,
        IsTrivialZetaZero (rho : Complex) -> system.weight f rho = 0 := by
  intro f rho htrivial
  exact
    system.weight_eq_zero_of_zeroArgument_extension_eq_zero f rho
      (htrivial_extension f rho htrivial)

end SchwartzRiemannWeilExtensionSystem

/--
The completed-zeta normalized zero-side weight: keep the project weight on
nontrivial zeroes and remove the project-known trivial zeroes from the zero
side.

This keeps `ZetaZeroSubtype` stable while making the completed-zeta
normalization explicit: trivial-zero contributions belong to the gamma/real
place normalization, not to the p-series zero-side weight.
-/
noncomputable def completedZetaNormalizedZeroWeight
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) : Real :=
  by
    classical
    exact if IsTrivialZetaZero (rho : Complex) then 0 else system.weight f rho

/-- Project-known trivial zeroes vanish in the completed-zeta normalized weight. -/
@[simp]
theorem completedZetaNormalizedZeroWeight_eq_zero_of_trivial
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (htrivial : IsTrivialZetaZero (rho : Complex)) :
    completedZetaNormalizedZeroWeight system f rho = 0 := by
  classical
  simp [completedZetaNormalizedZeroWeight, htrivial]

/-- Nontrivial zeroes keep the original project-side real weight. -/
@[simp]
theorem completedZetaNormalizedZeroWeight_eq_weight_of_not_trivial
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    completedZetaNormalizedZeroWeight system f rho = system.weight f rho := by
  classical
  simp [completedZetaNormalizedZeroWeight, hnotTrivial]

/-- The set of zeta zeroes that are not project-known trivial zeroes. -/
def nontrivialZetaZeroSet : Set ZetaZeroSubtype :=
  {rho : ZetaZeroSubtype | Not (IsTrivialZetaZero (rho : Complex))}

/-- The subtype of zeta zeroes that remain on the completed-zeta zero side. -/
abbrev NontrivialZetaZeroSubtype : Type :=
  ↑nontrivialZetaZeroSet

/-- The original project weight, restricted to nontrivial zeroes. -/
noncomputable def nontrivialZetaZeroWeight
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (rho : ↑nontrivialZetaZeroSet) : Real :=
  system.weight f (rho : ZetaZeroSubtype)

/-- Filter a finite zeta-zero window to the zeroes that remain on the normalized zero side. -/
noncomputable def nontrivialZetaZeroFinset
    (zeroes : Finset ZetaZeroSubtype) : Finset ZetaZeroSubtype := by
  classical
  exact zeroes.filter (fun rho : ZetaZeroSubtype => rho ∈ nontrivialZetaZeroSet)

/--
The completed-zeta normalized weight is the indicator of the nontrivial-zero
subtype, applied to the original project weight.
-/
theorem completedZetaNormalizedZeroWeight_eq_nontrivialZetaZeroSet_indicator
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    completedZetaNormalizedZeroWeight system f =
      nontrivialZetaZeroSet.indicator (system.weight f) := by
  classical
  funext rho
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · simp [completedZetaNormalizedZeroWeight, nontrivialZetaZeroSet, htrivial]
  · simp [completedZetaNormalizedZeroWeight, nontrivialZetaZeroSet, htrivial]

/--
Finite sums of the completed-zeta normalized weight are sums over the
nontrivial-zero subwindow of the original project weight.
-/
theorem sum_completedZetaNormalizedZeroWeight_eq_sum_nontrivialZetaZeroFinset
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (zeroes : Finset ZetaZeroSubtype) :
    zeroes.sum (completedZetaNormalizedZeroWeight system f) =
      (nontrivialZetaZeroFinset zeroes).sum (system.weight f) := by
  classical
  unfold nontrivialZetaZeroFinset
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho _hrho
  simpa [Set.indicator] using
    congrFun
      (completedZetaNormalizedZeroWeight_eq_nontrivialZetaZeroSet_indicator
        system f) rho

/--
Summability of the completed-zeta normalized all-zero weight is equivalent to
summability of the raw project weight over nontrivial zeroes.
-/
theorem summable_completedZetaNormalizedZeroWeight_iff_summable_nontrivialZetaZeroWeight
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    Summable (completedZetaNormalizedZeroWeight system f) ↔
      Summable (nontrivialZetaZeroWeight system f) := by
  classical
  constructor
  · intro hsummable
    have hsummable_indicator :
        Summable (nontrivialZetaZeroSet.indicator (system.weight f)) := by
      simpa [completedZetaNormalizedZeroWeight_eq_nontrivialZetaZeroSet_indicator] using
        hsummable
    change
      Summable
        (fun rho : ↑nontrivialZetaZeroSet =>
          system.weight f (rho : ZetaZeroSubtype))
    simpa [Function.comp_def] using
      (summable_subtype_iff_indicator
        (s := nontrivialZetaZeroSet) (f := system.weight f)).mpr
        hsummable_indicator
  · intro hsummable
    have hsummable_restricted :
        Summable
          (fun rho : ↑nontrivialZetaZeroSet =>
            system.weight f (rho : ZetaZeroSubtype)) := by
      change
        Summable
          (fun rho : ↑nontrivialZetaZeroSet =>
            system.weight f (rho : ZetaZeroSubtype)) at hsummable
      exact hsummable
    have hsummable_indicator :
        Summable (nontrivialZetaZeroSet.indicator (system.weight f)) := by
      exact
        (summable_subtype_iff_indicator
          (s := nontrivialZetaZeroSet) (f := system.weight f)).mp
          (by simpa [Function.comp_def] using hsummable_restricted)
    simpa [completedZetaNormalizedZeroWeight_eq_nontrivialZetaZeroSet_indicator] using
      hsummable_indicator

/--
The completed-zeta normalized zero-side sum is exactly the sum over the
nontrivial-zero subtype.
-/
theorem tsum_completedZetaNormalizedZeroWeight_eq_tsum_nontrivialZetaZeroWeight
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    tsum (completedZetaNormalizedZeroWeight system f) =
      tsum (nontrivialZetaZeroWeight system f) := by
  classical
  calc
    tsum (completedZetaNormalizedZeroWeight system f) =
        tsum (nontrivialZetaZeroSet.indicator (system.weight f)) := by
      apply tsum_congr
      intro rho
      rw [completedZetaNormalizedZeroWeight_eq_nontrivialZetaZeroSet_indicator]
    _ = tsum (nontrivialZetaZeroWeight system f) := by
      change
        tsum (nontrivialZetaZeroSet.indicator (system.weight f)) =
          tsum
            (fun rho : ↑nontrivialZetaZeroSet =>
              system.weight f (rho : ZetaZeroSubtype))
      simpa [Function.comp_def] using
        (tsum_subtype nontrivialZetaZeroSet (system.weight f)).symm

/--
The norm of the completed-zeta normalized weight is the indicator of the
nontrivial-zero subtype, applied to the norm of the original project weight.
-/
theorem norm_completedZetaNormalizedZeroWeight_eq_nontrivialZetaZeroSet_indicator_norm_weight
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    (fun rho : ZetaZeroSubtype =>
        norm (completedZetaNormalizedZeroWeight system f rho)) =
      nontrivialZetaZeroSet.indicator
        (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) := by
  classical
  funext rho
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · simp [completedZetaNormalizedZeroWeight, nontrivialZetaZeroSet, htrivial]
  · simp [completedZetaNormalizedZeroWeight, nontrivialZetaZeroSet, htrivial]

/--
Absolute summability of the completed-zeta normalized all-zero weight is
equivalent to absolute summability of the raw project weight over nontrivial
zeroes.
-/
theorem summable_norm_completedZetaNormalizedZeroWeight_iff_summable_norm_nontrivialZetaZeroWeight
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    Summable
        (fun rho : ZetaZeroSubtype =>
          norm (completedZetaNormalizedZeroWeight system f rho)) ↔
      Summable
        (fun rho : ↑nontrivialZetaZeroSet =>
          norm (nontrivialZetaZeroWeight system f rho)) := by
  classical
  constructor
  · intro hsummable
    have hsummable_indicator :
        Summable
          (nontrivialZetaZeroSet.indicator
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho))) := by
      rw [← norm_completedZetaNormalizedZeroWeight_eq_nontrivialZetaZeroSet_indicator_norm_weight]
      exact hsummable
    change
      Summable
        (fun rho : ↑nontrivialZetaZeroSet =>
          norm (system.weight f (rho : ZetaZeroSubtype)))
    simpa [nontrivialZetaZeroWeight, Function.comp_def] using
      (summable_subtype_iff_indicator
        (s := nontrivialZetaZeroSet)
        (f := fun rho : ZetaZeroSubtype => norm (system.weight f rho))).mpr
        hsummable_indicator
  · intro hsummable
    have hsummable_restricted :
        Summable
          (fun rho : ↑nontrivialZetaZeroSet =>
            norm (system.weight f (rho : ZetaZeroSubtype))) := by
      change
        Summable
          (fun rho : ↑nontrivialZetaZeroSet =>
            norm (system.weight f (rho : ZetaZeroSubtype))) at hsummable
      exact hsummable
    have hsummable_indicator :
        Summable
          (nontrivialZetaZeroSet.indicator
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho))) := by
      exact
        (summable_subtype_iff_indicator
          (s := nontrivialZetaZeroSet)
          (f := fun rho : ZetaZeroSubtype => norm (system.weight f rho))).mp
          (by simpa [Function.comp_def] using hsummable_restricted)
    rw [norm_completedZetaNormalizedZeroWeight_eq_nontrivialZetaZeroSet_indicator_norm_weight]
    exact hsummable_indicator

/--
The absolute completed-zeta normalized zero-side sum is exactly the absolute
sum over the nontrivial-zero subtype.
-/
theorem tsum_norm_completedZetaNormalizedZeroWeight_eq_tsum_norm_nontrivialZetaZeroWeight
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    tsum
        (fun rho : ZetaZeroSubtype =>
          norm (completedZetaNormalizedZeroWeight system f rho)) =
      tsum
        (fun rho : ↑nontrivialZetaZeroSet =>
          norm (nontrivialZetaZeroWeight system f rho)) := by
  classical
  calc
    tsum
        (fun rho : ZetaZeroSubtype =>
          norm (completedZetaNormalizedZeroWeight system f rho)) =
        tsum
          (nontrivialZetaZeroSet.indicator
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho))) := by
      apply tsum_congr
      intro rho
      exact congrFun
        (norm_completedZetaNormalizedZeroWeight_eq_nontrivialZetaZeroSet_indicator_norm_weight
          system f) rho
    _ =
        tsum
          (fun rho : ↑nontrivialZetaZeroSet =>
            norm (nontrivialZetaZeroWeight system f rho)) := by
      change
        tsum
            (nontrivialZetaZeroSet.indicator
              (fun rho : ZetaZeroSubtype => norm (system.weight f rho))) =
          tsum
            (fun rho : ↑nontrivialZetaZeroSet =>
              norm (system.weight f (rho : ZetaZeroSubtype)))
      simpa [Function.comp_def] using
        (tsum_subtype nontrivialZetaZeroSet
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho))).symm

namespace SchwartzRiemannWeilExtensionSystem

/--
Turn a candidate extension system into the zero-side interface using the
completed-zeta normalized weight.
-/
noncomputable def toCompletedZetaNormalizedZeroSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f)) :
    SchwartzRiemannWeilZeroSide where
  weight := completedZetaNormalizedZeroWeight system
  summable_weight := hsummable

/-- The normalized zero side has exactly the completed-zeta normalized weight. -/
theorem toCompletedZetaNormalizedZeroSide_weight
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    (system.toCompletedZetaNormalizedZeroSide hsummable).weight f rho =
      completedZetaNormalizedZeroWeight system f rho :=
  rfl

end SchwartzRiemannWeilExtensionSystem

/--
A named summability certificate for the candidate Riemann-Weil zero weight.

This is the next analytic work unit after choosing the complex zero
contribution: prove that the induced real-valued weight is summable over the
actual zeta zeroes for each Schwartz test function.
-/
structure SchwartzRiemannWeilWeightSummability
    (system : SchwartzRiemannWeilExtensionSystem) where
  summable_weight :
    forall f : SchwartzLineTestFunction, Summable (system.weight f)

namespace SchwartzRiemannWeilWeightSummability

/-- A summability certificate turns the candidate weight into the zero-side interface. -/
noncomputable def toZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilWeightSummability system) :
    SchwartzRiemannWeilZeroSide :=
  system.toZeroSide certificate.summable_weight

/-- The induced zero side has exactly the candidate Riemann-Weil weight. -/
theorem toZeroSide_weight
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilWeightSummability system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    certificate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for the certified weight converge to its global zero side. -/
theorem tendsto_windowZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilWeightSummability system)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => certificate.toZeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (certificate.toZeroSide.zeroSide f)) :=
  certificate.toZeroSide.tendsto_windowZeroSide exhaustion f

end SchwartzRiemannWeilWeightSummability

/--
Absolute convergence of the complex zero contribution.

This is a stronger, more natural analytic target than bare summability of the
real-valued weight. The checked bridge below proves that absolute convergence
of the complex values implies the summability certificate required by the
existing zero-side machinery.
-/
structure SchwartzRiemannWeilAbsoluteConvergence
    (system : SchwartzRiemannWeilExtensionSystem) where
  summable_norm_zeroValue :
    forall f : SchwartzLineTestFunction,
      Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho))

namespace SchwartzRiemannWeilAbsoluteConvergence

/-- Absolute convergence gives summability of the induced real-valued weight. -/
theorem summable_weight
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilAbsoluteConvergence system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  (certificate.summable_norm_zeroValue f).of_norm_bounded
    (system.norm_weight_le_norm_zeroValue f)

/-- Absolute convergence gives the named weight-summability certificate. -/
def toWeightSummability
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilAbsoluteConvergence system) :
    SchwartzRiemannWeilWeightSummability system where
  summable_weight := certificate.summable_weight

/-- Absolute convergence turns the candidate weight into the zero-side interface. -/
noncomputable def toZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilAbsoluteConvergence system) :
    SchwartzRiemannWeilZeroSide :=
  certificate.toWeightSummability.toZeroSide

/-- The zero side induced by absolute convergence has exactly the candidate weight. -/
theorem toZeroSide_weight
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilAbsoluteConvergence system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    certificate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for an absolutely convergent weight converge globally. -/
theorem tendsto_windowZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilAbsoluteConvergence system)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => certificate.toZeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (certificate.toZeroSide.zeroSide f)) :=
  certificate.toZeroSide.tendsto_windowZeroSide exhaustion f

end SchwartzRiemannWeilAbsoluteConvergence

/--
A summable real majorant for the complex zero contribution.

This is the most estimate-friendly form of the next analytic obligation:
produce a real function on the zeta-zero subtype that bounds the norm of the
candidate complex zero value and is summable for each Schwartz test function.
-/
structure SchwartzRiemannWeilNormMajorant
    (system : SchwartzRiemannWeilExtensionSystem) where
  majorant : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real
  summable_majorant :
    forall f : SchwartzLineTestFunction, Summable (majorant f)
  norm_zeroValue_le_majorant :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <= majorant f rho

namespace SchwartzRiemannWeilNormMajorant

/-- A majorant is nonnegative wherever it bounds the norm of the zero contribution. -/
theorem majorant_nonneg
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilNormMajorant system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    0 <= certificate.majorant f rho :=
  (norm_nonneg (system.zeroValue f rho)).trans
    (certificate.norm_zeroValue_le_majorant f rho)

/-- A summable norm-majorant makes the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilNormMajorant system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) := by
  exact Summable.of_nonneg_of_le
    (fun rho : ZetaZeroSubtype => norm_nonneg (system.zeroValue f rho))
    (fun rho : ZetaZeroSubtype =>
      certificate.norm_zeroValue_le_majorant f rho)
    (certificate.summable_majorant f)

/-- A summable norm-majorant gives absolute convergence of the complex zero contribution. -/
def toAbsoluteConvergence
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilNormMajorant system) :
    SchwartzRiemannWeilAbsoluteConvergence system where
  summable_norm_zeroValue := certificate.summable_norm_zeroValue

/-- A summable norm-majorant gives summability of the induced real-valued weight. -/
def toWeightSummability
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilNormMajorant system) :
    SchwartzRiemannWeilWeightSummability system :=
  certificate.toAbsoluteConvergence.toWeightSummability

/-- A summable norm-majorant turns the candidate weight into the zero-side interface. -/
noncomputable def toZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilNormMajorant system) :
    SchwartzRiemannWeilZeroSide :=
  certificate.toWeightSummability.toZeroSide

/-- The zero side induced by a norm-majorant has exactly the candidate weight. -/
theorem toZeroSide_weight
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilNormMajorant system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    certificate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for a dominated candidate weight converge globally. -/
theorem tendsto_windowZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilNormMajorant system)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => certificate.toZeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (certificate.toZeroSide.zeroSide f)) :=
  certificate.toZeroSide.tendsto_windowZeroSide exhaustion f

end SchwartzRiemannWeilNormMajorant

/--
An encoded shell majorant for the complex zero contribution.

The map `encode` places each zeta zero into a shell-coded indexing type
`Sigma fiber`. If the shell-coded majorant is summable and dominates the zero
contribution after encoding, then injective reindexing gives the ordinary
norm-majorant on actual zeta zeroes.
-/
structure SchwartzRiemannWeilEncodedShellMajorant
    (system : SchwartzRiemannWeilExtensionSystem) where
  fiber : Nat -> Type
  encode : ZetaZeroSubtype -> Sigma fiber
  encode_injective : Function.Injective encode
  shellMajorant : SchwartzLineTestFunction -> Sigma fiber -> Real
  summable_shellMajorant :
    forall f : SchwartzLineTestFunction, Summable (shellMajorant f)
  norm_zeroValue_le_shellMajorant :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <= shellMajorant f (encode rho)

namespace SchwartzRiemannWeilEncodedShellMajorant

/-- An encoded shell majorant induces the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilEncodedShellMajorant system) :
    SchwartzRiemannWeilNormMajorant system where
  majorant := fun f rho => certificate.shellMajorant f (certificate.encode rho)
  summable_majorant := fun f => by
    simpa [Function.comp_def] using
      (certificate.summable_shellMajorant f).comp_injective
        certificate.encode_injective
  norm_zeroValue_le_majorant := certificate.norm_zeroValue_le_shellMajorant

/-- An encoded shell majorant gives absolute convergence of the complex zero contribution. -/
def toAbsoluteConvergence
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilEncodedShellMajorant system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  certificate.toNormMajorant.toAbsoluteConvergence

/-- An encoded shell majorant gives summability of the induced real-valued weight. -/
def toWeightSummability
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilEncodedShellMajorant system) :
    SchwartzRiemannWeilWeightSummability system :=
  certificate.toNormMajorant.toWeightSummability

/-- An encoded shell majorant turns the candidate weight into the zero-side interface. -/
noncomputable def toZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilEncodedShellMajorant system) :
    SchwartzRiemannWeilZeroSide :=
  certificate.toWeightSummability.toZeroSide

/-- The zero side induced by an encoded shell majorant has exactly the candidate weight. -/
theorem toZeroSide_weight
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilEncodedShellMajorant system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    certificate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for an encoded-shell dominated weight converge globally. -/
theorem tendsto_windowZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilEncodedShellMajorant system)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => certificate.toZeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (certificate.toZeroSide.zeroSide f)) :=
  certificate.toZeroSide.tendsto_windowZeroSide exhaustion f

end SchwartzRiemannWeilEncodedShellMajorant

/--
A finite-fiber shell majorant.

This is the one-dimensional estimate form expected from zero-counting
arguments: each shell has finitely many encoded zero slots, every zero in that
shell is bounded by `shellBound f n`, and the shell totals
`card shell * shellBound` form a summable series.
-/
structure SchwartzRiemannWeilFiniteShellMajorant
    (system : SchwartzRiemannWeilExtensionSystem) where
  fiber : Nat -> Type
  fiber_fintype : forall n : Nat, Fintype (fiber n)
  encode : ZetaZeroSubtype -> Sigma fiber
  encode_injective : Function.Injective encode
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  summable_shellTotal :
    forall f : SchwartzLineTestFunction,
      Summable (fun n : Nat =>
        (@Fintype.card (fiber n) (fiber_fintype n) : Real) * shellBound f n)
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <= shellBound f (encode rho).1

namespace SchwartzRiemannWeilFiniteShellMajorant

/-- The finite-fiber shell total is the `tsum` over that shell. -/
theorem tsum_shellBound_eq_shellTotal
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilFiniteShellMajorant system)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    (tsum fun _ : certificate.fiber n => certificate.shellBound f n) =
      (@Fintype.card (certificate.fiber n) (certificate.fiber_fintype n) : Real) *
        certificate.shellBound f n := by
  letI : Fintype (certificate.fiber n) := certificate.fiber_fintype n
  simp [tsum_fintype, Finset.sum_const, nsmul_eq_mul]

/-- A finite-fiber shell majorant induces an encoded-shell majorant. -/
noncomputable def toEncodedShellMajorant
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilFiniteShellMajorant system) :
    SchwartzRiemannWeilEncodedShellMajorant system where
  fiber := certificate.fiber
  encode := certificate.encode
  encode_injective := certificate.encode_injective
  shellMajorant := fun f p => certificate.shellBound f p.1
  summable_shellMajorant := fun f => by
    have hnonneg :
        forall p : Sigma certificate.fiber,
          0 <= certificate.shellBound f p.1 := by
      intro p
      exact certificate.shellBound_nonneg f p.1
    refine (summable_sigma_of_nonneg hnonneg).2 ?_
    constructor
    · intro n
      letI : Fintype (certificate.fiber n) := certificate.fiber_fintype n
      exact (hasSum_fintype
        (fun _ : certificate.fiber n => certificate.shellBound f n)).summable
    · simpa [certificate.tsum_shellBound_eq_shellTotal f] using
        certificate.summable_shellTotal f
  norm_zeroValue_le_shellMajorant := certificate.norm_zeroValue_le_shellBound

/-- A finite-fiber shell majorant induces the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilFiniteShellMajorant system) :
    SchwartzRiemannWeilNormMajorant system :=
  certificate.toEncodedShellMajorant.toNormMajorant

/-- A finite-fiber shell majorant makes the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilFiniteShellMajorant system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  certificate.toNormMajorant.summable_norm_zeroValue f

/-- A finite-fiber shell majorant gives absolute convergence of the complex zero contribution. -/
def toAbsoluteConvergence
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilFiniteShellMajorant system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  certificate.toNormMajorant.toAbsoluteConvergence

/-- A finite-fiber shell majorant gives summability of the induced real-valued weight. -/
def toWeightSummability
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilFiniteShellMajorant system) :
    SchwartzRiemannWeilWeightSummability system :=
  certificate.toNormMajorant.toWeightSummability

/-- A finite-fiber shell majorant turns the candidate weight into the zero-side interface. -/
noncomputable def toZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilFiniteShellMajorant system) :
    SchwartzRiemannWeilZeroSide :=
  certificate.toWeightSummability.toZeroSide

/-- The zero side induced by a finite-fiber shell majorant has exactly the candidate weight. -/
theorem toZeroSide_weight
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilFiniteShellMajorant system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    certificate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for finite-shell dominated weights converge globally. -/
theorem tendsto_windowZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilFiniteShellMajorant system)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => certificate.toZeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (certificate.toZeroSide.zeroSide f)) :=
  certificate.toZeroSide.tendsto_windowZeroSide exhaustion f

end SchwartzRiemannWeilFiniteShellMajorant

/--
A concrete finite-shell decomposition of the zeta-zero subtype.

The field `shell n` is a finite set of actual zeta zeroes, and
`existsUnique_mem_shell` says every zeta zero belongs to exactly one shell.
This packages the bookkeeping needed to turn shell-by-shell estimates into the
encoded finite-shell majorant interface.
-/
structure ZetaZeroFiniteShellDecomposition where
  shell : Nat -> Finset ZetaZeroSubtype
  existsUnique_mem_shell :
    forall rho : ZetaZeroSubtype, ExistsUnique fun n : Nat => rho ∈ shell n

namespace ZetaZeroFiniteShellDecomposition

/-- The finite fiber type of zeta zeroes in the `n`th shell. -/
def fiber (decomposition : ZetaZeroFiniteShellDecomposition) (n : Nat) : Type :=
  {rho : ZetaZeroSubtype // rho ∈ decomposition.shell n}

/-- The shell fiber is finite because it is represented by a finset. -/
@[reducible]
noncomputable def fiberFintype
    (decomposition : ZetaZeroFiniteShellDecomposition)
    (n : Nat) : Fintype (decomposition.fiber n) :=
  Fintype.ofFinset (decomposition.shell n) (by
    intro rho
    rfl)

/-- The canonical fiber cardinality is the cardinality of the corresponding shell finset. -/
theorem card_fiber
    (decomposition : ZetaZeroFiniteShellDecomposition)
    (n : Nat) :
    @Fintype.card (decomposition.fiber n) (decomposition.fiberFintype n) =
      (decomposition.shell n).card := by
  unfold fiber fiberFintype
  exact Fintype.card_coe (decomposition.shell n)

/-- The shell index of a zeta zero. -/
noncomputable def index
    (decomposition : ZetaZeroFiniteShellDecomposition)
    (rho : ZetaZeroSubtype) : Nat :=
  Classical.choose (decomposition.existsUnique_mem_shell rho)

/-- A zeta zero belongs to its chosen shell. -/
theorem mem_shell_index
    (decomposition : ZetaZeroFiniteShellDecomposition)
    (rho : ZetaZeroSubtype) :
    rho ∈ decomposition.shell (decomposition.index rho) :=
  (Classical.choose_spec (decomposition.existsUnique_mem_shell rho)).1

/-- Any shell containing a zero is its chosen shell. -/
theorem eq_index_of_mem_shell
    (decomposition : ZetaZeroFiniteShellDecomposition)
    {rho : ZetaZeroSubtype} {n : Nat}
    (hrho : rho ∈ decomposition.shell n) :
    n = decomposition.index rho :=
  (Classical.choose_spec (decomposition.existsUnique_mem_shell rho)).2 n hrho

/-- Encode a zeta zero by its shell index and its membership in that shell. -/
noncomputable def encode
    (decomposition : ZetaZeroFiniteShellDecomposition) :
    ZetaZeroSubtype -> Sigma decomposition.fiber :=
  fun rho =>
    ⟨decomposition.index rho,
      ⟨rho, decomposition.mem_shell_index rho⟩⟩

/-- The shell encoding remembers the underlying zeta zero. -/
theorem encode_injective
    (decomposition : ZetaZeroFiniteShellDecomposition) :
    Function.Injective decomposition.encode := by
  intro rho tau h
  simpa [encode] using
    congrArg (fun p : Sigma decomposition.fiber => p.2.1) h

/--
Turn a concrete finite-shell decomposition plus shell bounds into the abstract
finite-shell majorant interface.
-/
noncomputable def toFiniteShellMajorant
    (decomposition : ZetaZeroFiniteShellDecomposition)
    {system : SchwartzRiemannWeilExtensionSystem}
    (shellBound : SchwartzLineTestFunction -> Nat -> Real)
    (shellBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n)
    (summable_shellTotal :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat =>
          (@Fintype.card (decomposition.fiber n)
            (decomposition.fiberFintype n) : Real) * shellBound f n))
    (norm_zeroValue_le_shellBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (system.zeroValue f rho) <= shellBound f (decomposition.index rho)) :
    SchwartzRiemannWeilFiniteShellMajorant system where
  fiber := decomposition.fiber
  fiber_fintype := decomposition.fiberFintype
  encode := decomposition.encode
  encode_injective := decomposition.encode_injective
  shellBound := shellBound
  shellBound_nonneg := shellBound_nonneg
  summable_shellTotal := summable_shellTotal
  norm_zeroValue_le_shellBound := by
    intro f rho
    simpa [encode] using norm_zeroValue_le_shellBound f rho

/--
Variant of `toFiniteShellMajorant` whose shell-total hypothesis uses the
ordinary cardinality of the shell finset.
-/
noncomputable def toFiniteShellMajorantOfShellCard
    (decomposition : ZetaZeroFiniteShellDecomposition)
    {system : SchwartzRiemannWeilExtensionSystem}
    (shellBound : SchwartzLineTestFunction -> Nat -> Real)
    (shellBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n)
    (summable_shellTotal :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat =>
          ((decomposition.shell n).card : Real) * shellBound f n))
    (norm_zeroValue_le_shellBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (system.zeroValue f rho) <= shellBound f (decomposition.index rho)) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  decomposition.toFiniteShellMajorant
    shellBound
    shellBound_nonneg
    (fun f => by
      simpa [decomposition.card_fiber] using summable_shellTotal f)
    norm_zeroValue_le_shellBound

end ZetaZeroFiniteShellDecomposition

/-- The zeta zeroes that first appear in the `n`th window of a compact exhaustion. -/
noncomputable def ComplexCompactExhaustion.zetaZeroFirstEntryShell
    (exhaustion : ComplexCompactExhaustion) (n : Nat) : Finset ZetaZeroSubtype := by
  classical
  exact (exhaustion.zetaZeroSubtypeFinset n).filter
    (fun rho : ZetaZeroSubtype =>
      forall m : Nat, m < n -> rho ∉ exhaustion.zetaZeroSubtypeFinset m)

/-- Membership in an exhaustion first-entry shell. -/
theorem ComplexCompactExhaustion.mem_zetaZeroFirstEntryShell_iff
    (exhaustion : ComplexCompactExhaustion) (n : Nat) {rho : ZetaZeroSubtype} :
    rho ∈ exhaustion.zetaZeroFirstEntryShell n ↔
      rho ∈ exhaustion.zetaZeroSubtypeFinset n ∧
        forall m : Nat, m < n -> rho ∉ exhaustion.zetaZeroSubtypeFinset m := by
  classical
  simp [ComplexCompactExhaustion.zetaZeroFirstEntryShell]

/-- Every zeta zero appears in exactly one first-entry shell of a compact exhaustion. -/
theorem ComplexCompactExhaustion.existsUnique_mem_zetaZeroFirstEntryShell
    (exhaustion : ComplexCompactExhaustion)
    (rho : ZetaZeroSubtype) :
    ExistsUnique fun n : Nat => rho ∈ exhaustion.zetaZeroFirstEntryShell n := by
  classical
  have hexists : ∃ n : Nat, rho ∈ exhaustion.zetaZeroSubtypeFinset n :=
    (exhaustion.eventually_mem_zetaZeroSubtypeFinset rho).exists
  let n0 := Nat.find hexists
  refine ⟨n0, ?_, ?_⟩
  · exact (exhaustion.mem_zetaZeroFirstEntryShell_iff n0).mpr
      ⟨Nat.find_spec hexists, fun m hm => Nat.find_min hexists hm⟩
  · intro n hn
    have hn_data := (exhaustion.mem_zetaZeroFirstEntryShell_iff n).mp hn
    have hn0_le_n : n0 ≤ n := Nat.find_min' hexists hn_data.1
    have hn_le_n0 : n ≤ n0 := by
      by_contra hnot
      have hn0_lt_n : n0 < n := Nat.lt_of_not_ge hnot
      exact hn_data.2 n0 hn0_lt_n (Nat.find_spec hexists)
    exact le_antisymm hn_le_n0 hn0_le_n

/--
Every compact exhaustion gives a concrete finite-shell decomposition by first
entry into the exhaustion windows.
-/
noncomputable def ComplexCompactExhaustion.toZetaZeroFiniteShellDecomposition
    (exhaustion : ComplexCompactExhaustion) :
    ZetaZeroFiniteShellDecomposition where
  shell := exhaustion.zetaZeroFirstEntryShell
  existsUnique_mem_shell := exhaustion.existsUnique_mem_zetaZeroFirstEntryShell

/-- The first-entry shell index of a zeta zero relative to a compact exhaustion. -/
noncomputable def ComplexCompactExhaustion.zetaZeroFirstEntryIndex
    (exhaustion : ComplexCompactExhaustion)
    (rho : ZetaZeroSubtype) : Nat :=
  exhaustion.toZetaZeroFiniteShellDecomposition.index rho

/-- A zeta zero belongs to its first-entry shell. -/
theorem ComplexCompactExhaustion.mem_zetaZeroFirstEntryIndex
    (exhaustion : ComplexCompactExhaustion)
    (rho : ZetaZeroSubtype) :
    rho ∈ exhaustion.zetaZeroFirstEntryShell
      (exhaustion.zetaZeroFirstEntryIndex rho) :=
  exhaustion.toZetaZeroFiniteShellDecomposition.mem_shell_index rho

/--
Build a finite-shell majorant directly from estimates on the first-entry shells
of a compact exhaustion.
-/
noncomputable def ComplexCompactExhaustion.toFiniteShellMajorantOfFirstEntryShells
    (exhaustion : ComplexCompactExhaustion)
    {system : SchwartzRiemannWeilExtensionSystem}
    (shellBound : SchwartzLineTestFunction -> Nat -> Real)
    (shellBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n)
    (summable_shellTotal :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat =>
          ((exhaustion.zetaZeroFirstEntryShell n).card : Real) * shellBound f n))
    (norm_zeroValue_le_shellBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (system.zeroValue f rho) <=
          shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  exhaustion.toZetaZeroFiniteShellDecomposition.toFiniteShellMajorantOfShellCard
    shellBound
    shellBound_nonneg
    summable_shellTotal
    norm_zeroValue_le_shellBound

/--
Build a finite-shell majorant from separate estimates for the number of new
zeroes in each first-entry shell and the size of each zero contribution there.
-/
noncomputable def ComplexCompactExhaustion.toFiniteShellMajorantOfFirstEntryBounds
    (exhaustion : ComplexCompactExhaustion)
    {system : SchwartzRiemannWeilExtensionSystem}
    (shellCardBound : Nat -> Real)
    (shellBound : SchwartzLineTestFunction -> Nat -> Real)
    (shellBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n)
    (shellCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n)
    (summable_boundTotal :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => shellCardBound n * shellBound f n))
    (norm_zeroValue_le_shellBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (system.zeroValue f rho) <=
          shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  exhaustion.toFiniteShellMajorantOfFirstEntryShells
    shellBound
    shellBound_nonneg
    (fun f => by
      refine Summable.of_nonneg_of_le ?_ ?_ (summable_boundTotal f)
      · intro n
        exact mul_nonneg (Nat.cast_nonneg _) (shellBound_nonneg f n)
      · intro n
        exact mul_le_mul_of_nonneg_right (shellCard_le n)
          (shellBound_nonneg f n))
    norm_zeroValue_le_shellBound

/--
Named shell estimate data for a compact exhaustion.

This is the concrete analytic target for the current zero-side summability
track: bound the number of first-entry zeroes in each shell, bound the size of
the complex zero contribution on that shell, and prove the resulting product
series is summable.
-/
structure SchwartzRiemannWeilFirstEntryShellEstimate
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  summable_boundTotal :
    forall f : SchwartzLineTestFunction,
      Summable (fun n : Nat => shellCardBound n * shellBound f n)
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilFirstEntryShellEstimate

/-- First-entry shell estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  exhaustion.toFiniteShellMajorantOfFirstEntryBounds
    estimate.shellCardBound
    estimate.shellBound
    estimate.shellBound_nonneg
    estimate.shellCard_le
    estimate.summable_boundTotal
    estimate.norm_zeroValue_le_shellBound

/-- First-entry shell estimates induce the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toFiniteShellMajorant.toNormMajorant

/-- First-entry shell estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toNormMajorant.summable_norm_zeroValue f

/-- First-entry shell estimates give absolute convergence of the complex zero contribution. -/
def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toNormMajorant.toAbsoluteConvergence

/-- First-entry shell estimates give summability of the induced real-valued weight. -/
def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toNormMajorant.toWeightSummability

/-- First-entry shell estimates make the induced real-valued weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  estimate.toWeightSummability.summable_weight f

/-- First-entry shell estimates turn the candidate weight into the zero-side interface. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- The zero side induced by first-entry shell estimates has exactly the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for first-entry shell estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilFirstEntryShellEstimate

/--
Geometric domination of first-entry shell totals.

This is a more checkable estimate package than an arbitrary summability proof:
the cardinality bound times the zero-value bound is dominated by a fixed
geometric series for each test function.
-/
structure SchwartzRiemannWeilGeometricFirstEntryShellEstimate
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  geometricConstant : SchwartzLineTestFunction -> Real
  geometricRatio : SchwartzLineTestFunction -> Real
  geometricRatio_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= geometricRatio f
  geometricRatio_lt_one :
    forall f : SchwartzLineTestFunction, geometricRatio f < 1
  geometricConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= geometricConstant f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  product_le_geometric :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellCardBound n * shellBound f n <=
        geometricConstant f * geometricRatio f ^ n
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilGeometricFirstEntryShellEstimate

/-- The geometric majorant makes the first-entry shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) := by
  refine Summable.of_nonneg_of_le
    (f := fun n : Nat =>
      estimate.geometricConstant f * estimate.geometricRatio f ^ n)
    (g := fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) ?_ ?_ ?_
  · intro n
    have hcard_nonneg : 0 <= estimate.shellCardBound n :=
      (Nat.cast_nonneg
        (exhaustion.zetaZeroFirstEntryShell n).card).trans
        (estimate.shellCard_le n)
    exact mul_nonneg hcard_nonneg (estimate.shellBound_nonneg f n)
  · intro n
    exact estimate.product_le_geometric f n
  · exact Summable.mul_left (estimate.geometricConstant f)
      (summable_geometric_of_lt_one (estimate.geometricRatio_nonneg f)
        (estimate.geometricRatio_lt_one f))

/-- Geometric first-entry estimates produce the named first-entry shell estimate. -/
def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system where
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  summable_boundTotal := estimate.summable_boundTotal
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- Geometric first-entry estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toFirstEntryShellEstimate.toFiniteShellMajorant

/-- Geometric first-entry estimates induce the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toFirstEntryShellEstimate.toNormMajorant

/-- Geometric first-entry estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toNormMajorant.summable_norm_zeroValue f

/-- Geometric first-entry estimates give absolute convergence of the complex zero contribution. -/
def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toFirstEntryShellEstimate.toAbsoluteConvergence

/-- Geometric first-entry estimates give summability of the induced real-valued weight. -/
def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toFirstEntryShellEstimate.toWeightSummability

/-- Geometric first-entry estimates make the induced real-valued weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  estimate.toWeightSummability.summable_weight f

/-- Geometric first-entry estimates turn the candidate weight into the zero-side interface. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- The zero side induced by geometric first-entry estimates has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for geometrically dominated weights converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilGeometricFirstEntryShellEstimate

/--
Eventual geometric domination of first-entry shell totals.

Analytic estimates often only settle into their clean asymptotic form after a
finite number of initial shells. This package allows those initial shells to be
arbitrary and asks for geometric domination only on the shifted tail.
-/
structure SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  geometricConstant : SchwartzLineTestFunction -> Real
  geometricRatio : SchwartzLineTestFunction -> Real
  geometricRatio_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= geometricRatio f
  geometricRatio_lt_one :
    forall f : SchwartzLineTestFunction, geometricRatio f < 1
  geometricConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= geometricConstant f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_product_le_geometric :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellCardBound (n + cutoff) * shellBound f (n + cutoff) <=
        geometricConstant f * geometricRatio f ^ n
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate

/-- The eventual geometric majorant makes all first-entry shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) := by
  rw [← @summable_nat_add_iff Real _ _ _ _ estimate.cutoff]
  refine Summable.of_nonneg_of_le
    (f := fun n : Nat =>
      estimate.geometricConstant f * estimate.geometricRatio f ^ n)
    (g := fun n : Nat =>
      estimate.shellCardBound (n + estimate.cutoff) *
        estimate.shellBound f (n + estimate.cutoff)) ?_ ?_ ?_
  · intro n
    have hcard_nonneg : 0 <= estimate.shellCardBound (n + estimate.cutoff) :=
      (Nat.cast_nonneg
        (exhaustion.zetaZeroFirstEntryShell (n + estimate.cutoff)).card).trans
        (estimate.shellCard_le (n + estimate.cutoff))
    exact mul_nonneg hcard_nonneg
      (estimate.shellBound_nonneg f (n + estimate.cutoff))
  · intro n
    exact estimate.tail_product_le_geometric f n
  · exact Summable.mul_left (estimate.geometricConstant f)
      (summable_geometric_of_lt_one (estimate.geometricRatio_nonneg f)
        (estimate.geometricRatio_lt_one f))

/-- Eventual geometric first-entry estimates produce the named shell estimate. -/
def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system where
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  summable_boundTotal := estimate.summable_boundTotal
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- Eventual geometric first-entry estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toFirstEntryShellEstimate.toFiniteShellMajorant

/-- Eventual geometric first-entry estimates induce the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toFirstEntryShellEstimate.toNormMajorant

/-- Eventual geometric first-entry estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toNormMajorant.summable_norm_zeroValue f

/-- Eventual geometric first-entry estimates give absolute convergence. -/
def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toFirstEntryShellEstimate.toAbsoluteConvergence

/-- Eventual geometric first-entry estimates give real-weight summability. -/
def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toFirstEntryShellEstimate.toWeightSummability

/-- Eventual geometric first-entry estimates make the induced real-valued weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  estimate.toWeightSummability.summable_weight f

/-- Eventual geometric first-entry estimates turn the candidate weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- The zero side induced by eventual geometric estimates has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for eventually dominated weights converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate

/--
Separated geometric estimates for first-entry shells.

This is the zero-counting shape expected in analytic work: one geometric bound
controls the number of zeroes entering each shell, while a test-function
dependent geometric bound controls the zero contribution on that shell. If the
product of the two ratios is below one, this data produces the geometric
first-entry shell certificate.
-/
structure SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  shellCardConstant : Real
  shellCardRatio : Real
  zeroBoundConstant : SchwartzLineTestFunction -> Real
  zeroBoundRatio : SchwartzLineTestFunction -> Real
  shellCardConstant_nonneg : 0 <= shellCardConstant
  shellCardRatio_nonneg : 0 <= shellCardRatio
  zeroBoundConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroBoundConstant f
  zeroBoundRatio_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroBoundRatio f
  product_ratio_lt_one :
    forall f : SchwartzLineTestFunction, shellCardRatio * zeroBoundRatio f < 1
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <=
        shellCardConstant * shellCardRatio ^ n
  norm_zeroValue_le_zeroBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        zeroBoundConstant f *
          zeroBoundRatio f ^ exhaustion.zetaZeroFirstEntryIndex rho

namespace SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate

/-- Separated count-and-decay estimates produce a geometric shell estimate. -/
def toGeometricFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilGeometricFirstEntryShellEstimate exhaustion system where
  shellCardBound := fun n =>
    estimate.shellCardConstant * estimate.shellCardRatio ^ n
  shellBound := fun f n =>
    estimate.zeroBoundConstant f * estimate.zeroBoundRatio f ^ n
  geometricConstant := fun f =>
    estimate.shellCardConstant * estimate.zeroBoundConstant f
  geometricRatio := fun f =>
    estimate.shellCardRatio * estimate.zeroBoundRatio f
  geometricRatio_nonneg := fun f =>
    mul_nonneg estimate.shellCardRatio_nonneg
      (estimate.zeroBoundRatio_nonneg f)
  geometricRatio_lt_one := estimate.product_ratio_lt_one
  geometricConstant_nonneg := fun f =>
    mul_nonneg estimate.shellCardConstant_nonneg
      (estimate.zeroBoundConstant_nonneg f)
  shellBound_nonneg := fun f n =>
    mul_nonneg (estimate.zeroBoundConstant_nonneg f)
      (pow_nonneg (estimate.zeroBoundRatio_nonneg f) n)
  shellCard_le := estimate.shellCard_le
  product_le_geometric := fun f n => by
    rw [mul_pow]
    ring_nf
    exact le_rfl
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_zeroBound

/-- Separated estimates produce the named first-entry shell estimate. -/
def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system :=
  estimate.toGeometricFirstEntryShellEstimate.toFirstEntryShellEstimate

/-- Separated estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toGeometricFirstEntryShellEstimate.toFiniteShellMajorant

/-- Separated estimates induce the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toGeometricFirstEntryShellEstimate.toNormMajorant

/-- Separated estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toNormMajorant.summable_norm_zeroValue f

/-- Separated estimates give absolute convergence of the complex zero contribution. -/
def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toGeometricFirstEntryShellEstimate.toAbsoluteConvergence

/-- Separated estimates give summability of the induced real-valued weight. -/
def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toGeometricFirstEntryShellEstimate.toWeightSummability

/-- Separated estimates make the induced real-valued weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  estimate.toWeightSummability.summable_weight f

/-- Separated estimates turn the candidate weight into the zero-side interface. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- The zero side induced by separated estimates has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for separated geometric estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate
        exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilSeparatedGeometricFirstEntryShellEstimate

/--
Eventual separated geometric estimates for first-entry shells.

This is the most estimate-friendly shell interface in this file. It keeps
arbitrary first-entry cardinality and zero-value bounds for all shells, but only
asks the separated count and decay estimates to hold on the shifted tail.
-/
structure SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellCardConstant : Real
  shellCardRatio : Real
  zeroBoundConstant : SchwartzLineTestFunction -> Real
  zeroBoundRatio : SchwartzLineTestFunction -> Real
  shellCardConstant_nonneg : 0 <= shellCardConstant
  shellCardRatio_nonneg : 0 <= shellCardRatio
  zeroBoundConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroBoundConstant f
  zeroBoundRatio_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroBoundRatio f
  product_ratio_lt_one :
    forall f : SchwartzLineTestFunction, shellCardRatio * zeroBoundRatio f < 1
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_shellCardBound_le :
    forall n : Nat,
      shellCardBound (n + cutoff) <= shellCardConstant * shellCardRatio ^ n
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <= zeroBoundConstant f * zeroBoundRatio f ^ n
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate

/-- Eventual separated estimates produce an eventual geometric shell estimate. -/
def toEventualGeometricFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
      exhaustion system where
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  geometricConstant := fun f =>
    estimate.shellCardConstant * estimate.zeroBoundConstant f
  geometricRatio := fun f =>
    estimate.shellCardRatio * estimate.zeroBoundRatio f
  geometricRatio_nonneg := fun f =>
    mul_nonneg estimate.shellCardRatio_nonneg
      (estimate.zeroBoundRatio_nonneg f)
  geometricRatio_lt_one := estimate.product_ratio_lt_one
  geometricConstant_nonneg := fun f =>
    mul_nonneg estimate.shellCardConstant_nonneg
      (estimate.zeroBoundConstant_nonneg f)
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  tail_product_le_geometric := fun f n => by
    have hcardMajorant_nonneg :
        0 <= estimate.shellCardConstant * estimate.shellCardRatio ^ n :=
      mul_nonneg estimate.shellCardConstant_nonneg
        (pow_nonneg estimate.shellCardRatio_nonneg n)
    calc
      estimate.shellCardBound (n + estimate.cutoff) *
          estimate.shellBound f (n + estimate.cutoff)
          <=
            (estimate.shellCardConstant * estimate.shellCardRatio ^ n) *
              (estimate.zeroBoundConstant f * estimate.zeroBoundRatio f ^ n) :=
        mul_le_mul (estimate.tail_shellCardBound_le n)
          (estimate.tail_shellBound_le f n)
          (estimate.shellBound_nonneg f (n + estimate.cutoff))
          hcardMajorant_nonneg
      _ <=
            (estimate.shellCardConstant * estimate.zeroBoundConstant f) *
              (estimate.shellCardRatio * estimate.zeroBoundRatio f) ^ n := by
        rw [mul_pow]
        ring_nf
        exact le_rfl
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- Eventual separated estimates produce the named first-entry shell estimate. -/
def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system :=
  estimate.toEventualGeometricFirstEntryShellEstimate.toFirstEntryShellEstimate

/-- Eventual separated estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toEventualGeometricFirstEntryShellEstimate.toFiniteShellMajorant

/-- Eventual separated estimates induce the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toEventualGeometricFirstEntryShellEstimate.toNormMajorant

/-- Eventual separated estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toNormMajorant.summable_norm_zeroValue f

/-- Eventual separated estimates give absolute convergence. -/
def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toEventualGeometricFirstEntryShellEstimate.toAbsoluteConvergence

/-- Eventual separated estimates give real-weight summability. -/
def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toEventualGeometricFirstEntryShellEstimate.toWeightSummability

/-- Eventual separated estimates make the induced real-valued weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  estimate.toWeightSummability.summable_weight f

/-- Eventual separated estimates turn the candidate weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- The zero side induced by eventual separated estimates has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for eventual separated estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate

/--
Eventual summable tail majorants for first-entry shell totals.

This is the broad comparison-test interface behind the more concrete geometric
packages above. It allows arbitrary first-entry shell bounds, but asks that the
tail of the product `shellCardBound * shellBound` be dominated by any summable
real sequence.
-/
structure SchwartzRiemannWeilEventualSummableTailMajorant
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  tailMajorant : SchwartzLineTestFunction -> Nat -> Real
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  summable_tailMajorant :
    forall f : SchwartzLineTestFunction, Summable (tailMajorant f)
  tail_product_le_majorant :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellCardBound (n + cutoff) * shellBound f (n + cutoff) <=
        tailMajorant f n
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilEventualSummableTailMajorant

/-- Eventual geometric estimates are a special case of summable tail majorants. -/
def ofEventualGeometric
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system where
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  tailMajorant := fun f n =>
    estimate.geometricConstant f * estimate.geometricRatio f ^ n
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  summable_tailMajorant := fun f =>
    Summable.mul_left (estimate.geometricConstant f)
      (summable_geometric_of_lt_one (estimate.geometricRatio_nonneg f)
        (estimate.geometricRatio_lt_one f))
  tail_product_le_majorant := estimate.tail_product_le_geometric
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- Eventual separated geometric estimates are a special case of tail majorants. -/
def ofEventualSeparatedGeometric
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedGeometricFirstEntryShellEstimate
        exhaustion system) :
    SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system :=
  ofEventualGeometric estimate.toEventualGeometricFirstEntryShellEstimate

/-- A summable tail majorant makes all first-entry shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) := by
  rw [← @summable_nat_add_iff Real _ _ _ _ estimate.cutoff]
  refine Summable.of_nonneg_of_le
    (f := estimate.tailMajorant f)
    (g := fun n : Nat =>
      estimate.shellCardBound (n + estimate.cutoff) *
        estimate.shellBound f (n + estimate.cutoff)) ?_ ?_
    (estimate.summable_tailMajorant f)
  · intro n
    have hcard_nonneg : 0 <= estimate.shellCardBound (n + estimate.cutoff) :=
      (Nat.cast_nonneg
        (exhaustion.zetaZeroFirstEntryShell (n + estimate.cutoff)).card).trans
        (estimate.shellCard_le (n + estimate.cutoff))
    exact mul_nonneg hcard_nonneg
      (estimate.shellBound_nonneg f (n + estimate.cutoff))
  · intro n
    exact estimate.tail_product_le_majorant f n

/-- Eventual summable tail majorants produce the named first-entry shell estimate. -/
def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system where
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  summable_boundTotal := estimate.summable_boundTotal
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- Eventual summable tail majorants produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toFirstEntryShellEstimate.toFiniteShellMajorant

/-- Eventual summable tail majorants induce the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toFirstEntryShellEstimate.toNormMajorant

/-- Eventual summable tail majorants make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toNormMajorant.summable_norm_zeroValue f

/-- Eventual summable tail majorants give absolute convergence. -/
def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toFirstEntryShellEstimate.toAbsoluteConvergence

/-- Eventual summable tail majorants give real-weight summability. -/
def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toFirstEntryShellEstimate.toWeightSummability

/-- Eventual summable tail majorants turn the candidate weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- The zero side induced by an eventual tail majorant has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for eventual tail majorants converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilEventualSummableTailMajorant

/--
Eventual separated summable tail majorants for first-entry shell totals.

This package separates the two analytic estimates usually proved in practice:
a tail majorant for the number of zeroes entering each shell, and a
test-function-dependent tail majorant for the size of the zero contribution on
that shell. If the product of those two tail majorants is summable, the broad
eventual tail-majorant interface follows.
-/
structure SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellCardTailMajorant : Nat -> Real
  zeroTailMajorant : SchwartzLineTestFunction -> Nat -> Real
  shellCardTailMajorant_nonneg :
    forall n : Nat, 0 <= shellCardTailMajorant n
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  summable_tailProduct :
    forall f : SchwartzLineTestFunction,
      Summable (fun n : Nat =>
        shellCardTailMajorant n * zeroTailMajorant f n)
  tail_shellCardBound_le :
    forall n : Nat,
      shellCardBound (n + cutoff) <= shellCardTailMajorant n
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <= zeroTailMajorant f n
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilEventualSeparatedSummableTailMajorant

/-- Separated summable tail estimates produce the broad tail-majorant certificate. -/
def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system where
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  tailMajorant := fun f n =>
    estimate.shellCardTailMajorant n * estimate.zeroTailMajorant f n
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  summable_tailMajorant := estimate.summable_tailProduct
  tail_product_le_majorant := fun f n =>
    mul_le_mul (estimate.tail_shellCardBound_le n)
      (estimate.tail_shellBound_le f n)
      (estimate.shellBound_nonneg f (n + estimate.cutoff))
      (estimate.shellCardTailMajorant_nonneg n)
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- Separated summable tail estimates produce the named first-entry shell estimate. -/
def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system :=
  estimate.toEventualSummableTailMajorant.toFirstEntryShellEstimate

/-- Separated summable tail estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toEventualSummableTailMajorant.toFiniteShellMajorant

/-- Separated summable tail estimates induce the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toEventualSummableTailMajorant.toNormMajorant

/-- Separated summable tail estimates give absolute convergence. -/
def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toEventualSummableTailMajorant.toAbsoluteConvergence

/-- Separated summable tail estimates give real-weight summability. -/
def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toEventualSummableTailMajorant.toWeightSummability

/-- Separated summable tail estimates turn the candidate weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- The zero side induced by separated summable tails has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for separated summable tails converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSeparatedSummableTailMajorant
        exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilEventualSeparatedSummableTailMajorant

/--
Eventual p-series tail majorants for first-entry shell totals.

This is a concrete summable-tail route: after a finite cutoff, the shell totals
are dominated by `C_f / |n + a_f| ^ s_f` with `1 < s_f`.
-/
structure SchwartzRiemannWeilEventualPSeriesTailMajorant
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  constant : SchwartzLineTestFunction -> Real
  shift : SchwartzLineTestFunction -> Real
  exponent : SchwartzLineTestFunction -> Real
  constant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= constant f
  one_lt_exponent :
    forall f : SchwartzLineTestFunction, 1 < exponent f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_product_le_pseries :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellCardBound (n + cutoff) * shellBound f (n + cutoff) <=
        constant f * (1 / |(n : Real) + shift f| ^ exponent f)
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilEventualPSeriesTailMajorant

/-- P-series tail estimates produce the general summable-tail majorant. -/
noncomputable def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system) :
    SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system where
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  tailMajorant := fun f n =>
    estimate.constant f * (1 / |(n : Real) + estimate.shift f| ^
      estimate.exponent f)
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  summable_tailMajorant := fun f =>
    Summable.mul_left (estimate.constant f)
      ((Real.summable_one_div_nat_add_rpow
        (estimate.shift f) (estimate.exponent f)).2
        (estimate.one_lt_exponent f))
  tail_product_le_majorant := estimate.tail_product_le_pseries
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- P-series tail estimates make all first-entry shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) :=
  estimate.toEventualSummableTailMajorant.summable_boundTotal f

/-- P-series tail estimates produce the named first-entry shell estimate. -/
noncomputable def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system :=
  estimate.toEventualSummableTailMajorant.toFirstEntryShellEstimate

/-- P-series tail estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toEventualSummableTailMajorant.toFiniteShellMajorant

/-- P-series tail estimates induce the standard norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toEventualSummableTailMajorant.toNormMajorant

/-- P-series tail estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toNormMajorant.summable_norm_zeroValue f

/-- P-series tail estimates give absolute convergence. -/
noncomputable def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toEventualSummableTailMajorant.toAbsoluteConvergence

/-- P-series tail estimates give real-weight summability. -/
noncomputable def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toEventualSummableTailMajorant.toWeightSummability

/-- P-series tail estimates turn the candidate weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- P-series tail estimates make the extension-induced zero-side weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  estimate.toWeightSummability.summable_weight f

/-- The zero side induced by a p-series tail estimate has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for p-series tail estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilEventualPSeriesTailMajorant

/--
An extension-independent finite-fiber shell majorant for a zero-side weight.

This is the same summability mechanism as `SchwartzRiemannWeilFiniteShellMajorant`,
but the weight is supplied directly rather than induced from a global
`SchwartzRiemannWeilExtensionSystem`. It is the natural target for restricted
source or dense-core routes where the eventual zero-side weight is known, but a
global all-Schwartz entire extension is not available.
-/
structure SchwartzRiemannWeilAbstractFiniteShellMajorant where
  weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real
  fiber : Nat -> Type
  fiber_fintype : forall n : Nat, Fintype (fiber n)
  encode : ZetaZeroSubtype -> Sigma fiber
  encode_injective : Function.Injective encode
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  summable_shellTotal :
    forall f : SchwartzLineTestFunction,
      Summable (fun n : Nat =>
        (@Fintype.card (fiber n) (fiber_fintype n) : Real) * shellBound f n)
  norm_weight_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (weight f rho) <= shellBound f (encode rho).1

namespace SchwartzRiemannWeilAbstractFiniteShellMajorant

/-- The encoded shell majorant associated to an abstract finite-shell certificate. -/
noncomputable def shellMajorant
    (certificate : SchwartzRiemannWeilAbstractFiniteShellMajorant)
    (f : SchwartzLineTestFunction) : Sigma certificate.fiber -> Real :=
  fun p => certificate.shellBound f p.1

/-- The finite-fiber shell total is the `tsum` over that shell. -/
theorem tsum_shellBound_eq_shellTotal
    (certificate : SchwartzRiemannWeilAbstractFiniteShellMajorant)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    (tsum fun _ : certificate.fiber n => certificate.shellBound f n) =
      (@Fintype.card (certificate.fiber n) (certificate.fiber_fintype n) : Real) *
        certificate.shellBound f n := by
  letI : Fintype (certificate.fiber n) := certificate.fiber_fintype n
  simp [tsum_fintype, Finset.sum_const, nsmul_eq_mul]

/-- An abstract finite-fiber shell majorant is summable on the encoded shell type. -/
theorem summable_shellMajorant
    (certificate : SchwartzRiemannWeilAbstractFiniteShellMajorant)
    (f : SchwartzLineTestFunction) :
    Summable (certificate.shellMajorant f) := by
  have hnonneg :
      forall p : Sigma certificate.fiber,
        0 <= certificate.shellBound f p.1 := by
    intro p
    exact certificate.shellBound_nonneg f p.1
  refine (summable_sigma_of_nonneg hnonneg).2 ?_
  constructor
  · intro n
    letI : Fintype (certificate.fiber n) := certificate.fiber_fintype n
    exact (hasSum_fintype
      (fun _ : certificate.fiber n => certificate.shellBound f n)).summable
  · simpa [certificate.tsum_shellBound_eq_shellTotal f] using
      certificate.summable_shellTotal f

/-- An abstract finite-shell majorant gives absolute summability of the supplied weight. -/
theorem summable_norm_weight
    (certificate : SchwartzRiemannWeilAbstractFiniteShellMajorant)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (certificate.weight f rho)) := by
  have hmajorant :
      Summable (fun rho : ZetaZeroSubtype =>
        certificate.shellBound f (certificate.encode rho).1) := by
    simpa [SchwartzRiemannWeilAbstractFiniteShellMajorant.shellMajorant,
      Function.comp_def] using
      (certificate.summable_shellMajorant f).comp_injective
        certificate.encode_injective
  exact Summable.of_nonneg_of_le
    (fun rho : ZetaZeroSubtype => norm_nonneg (certificate.weight f rho))
    (fun rho : ZetaZeroSubtype => certificate.norm_weight_le_shellBound f rho)
    hmajorant

/-- An abstract finite-shell majorant gives summability of the supplied weight. -/
theorem summable_weight
    (certificate : SchwartzRiemannWeilAbstractFiniteShellMajorant)
    (f : SchwartzLineTestFunction) :
    Summable (certificate.weight f) := by
  have hmajorant :
      Summable (fun rho : ZetaZeroSubtype =>
        certificate.shellBound f (certificate.encode rho).1) := by
    simpa [SchwartzRiemannWeilAbstractFiniteShellMajorant.shellMajorant,
      Function.comp_def] using
      (certificate.summable_shellMajorant f).comp_injective
        certificate.encode_injective
  exact hmajorant.of_norm_bounded
    (fun rho => certificate.norm_weight_le_shellBound f rho)

/-- An abstract finite-shell majorant turns the supplied weight into a zero side. -/
noncomputable def toZeroSide
    (certificate : SchwartzRiemannWeilAbstractFiniteShellMajorant) :
    SchwartzRiemannWeilZeroSide where
  weight := certificate.weight
  summable_weight := certificate.summable_weight

/-- The induced zero side has exactly the supplied weight. -/
theorem toZeroSide_weight
    (certificate : SchwartzRiemannWeilAbstractFiniteShellMajorant)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    certificate.toZeroSide.weight f rho = certificate.weight f rho :=
  rfl

/-- Compact-exhaustion sums for an abstract finite-shell weight converge globally. -/
theorem tendsto_windowZeroSide
    (certificate : SchwartzRiemannWeilAbstractFiniteShellMajorant)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => certificate.toZeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (certificate.toZeroSide.zeroSide f)) :=
  certificate.toZeroSide.tendsto_windowZeroSide exhaustion f

end SchwartzRiemannWeilAbstractFiniteShellMajorant

namespace ZetaZeroFiniteShellDecomposition

/--
Turn a finite-shell decomposition plus bounds for a directly supplied weight
into the extension-independent finite-shell majorant interface.
-/
noncomputable def toAbstractFiniteShellMajorant
    (decomposition : ZetaZeroFiniteShellDecomposition)
    (weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real)
    (shellBound : SchwartzLineTestFunction -> Nat -> Real)
    (shellBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n)
    (summable_shellTotal :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat =>
          (@Fintype.card (decomposition.fiber n)
            (decomposition.fiberFintype n) : Real) * shellBound f n))
    (norm_weight_le_shellBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (weight f rho) <= shellBound f (decomposition.index rho)) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant where
  weight := weight
  fiber := decomposition.fiber
  fiber_fintype := decomposition.fiberFintype
  encode := decomposition.encode
  encode_injective := decomposition.encode_injective
  shellBound := shellBound
  shellBound_nonneg := shellBound_nonneg
  summable_shellTotal := summable_shellTotal
  norm_weight_le_shellBound := by
    intro f rho
    simpa [encode] using norm_weight_le_shellBound f rho

/--
Variant of `toAbstractFiniteShellMajorant` whose shell-total hypothesis uses
the ordinary cardinality of the shell finset.
-/
noncomputable def toAbstractFiniteShellMajorantOfShellCard
    (decomposition : ZetaZeroFiniteShellDecomposition)
    (weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real)
    (shellBound : SchwartzLineTestFunction -> Nat -> Real)
    (shellBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n)
    (summable_shellTotal :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat =>
          ((decomposition.shell n).card : Real) * shellBound f n))
    (norm_weight_le_shellBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (weight f rho) <= shellBound f (decomposition.index rho)) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant :=
  decomposition.toAbstractFiniteShellMajorant
    weight
    shellBound
    shellBound_nonneg
    (fun f => by
      simpa [decomposition.card_fiber] using summable_shellTotal f)
    norm_weight_le_shellBound

end ZetaZeroFiniteShellDecomposition

/--
Build an abstract finite-shell majorant directly from estimates on the
first-entry shells of a compact exhaustion.
-/
noncomputable def ComplexCompactExhaustion.toAbstractFiniteShellMajorantOfFirstEntryShells
    (exhaustion : ComplexCompactExhaustion)
    (weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real)
    (shellBound : SchwartzLineTestFunction -> Nat -> Real)
    (shellBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n)
    (summable_shellTotal :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat =>
          ((exhaustion.zetaZeroFirstEntryShell n).card : Real) * shellBound f n))
    (norm_weight_le_shellBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (weight f rho) <=
          shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant :=
  exhaustion.toZetaZeroFiniteShellDecomposition.toAbstractFiniteShellMajorantOfShellCard
    weight
    shellBound
    shellBound_nonneg
    summable_shellTotal
    norm_weight_le_shellBound

/--
Build an abstract finite-shell majorant from separate first-entry shell
cardinality and weight-size estimates.
-/
noncomputable def ComplexCompactExhaustion.toAbstractFiniteShellMajorantOfFirstEntryBounds
    (exhaustion : ComplexCompactExhaustion)
    (weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real)
    (shellCardBound : Nat -> Real)
    (shellBound : SchwartzLineTestFunction -> Nat -> Real)
    (shellBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n)
    (shellCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n)
    (summable_boundTotal :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => shellCardBound n * shellBound f n))
    (norm_weight_le_shellBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (weight f rho) <=
          shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant :=
  exhaustion.toAbstractFiniteShellMajorantOfFirstEntryShells
    weight
    shellBound
    shellBound_nonneg
    (fun f => by
      refine Summable.of_nonneg_of_le ?_ ?_ (summable_boundTotal f)
      · intro n
        exact mul_nonneg (Nat.cast_nonneg _) (shellBound_nonneg f n)
      · intro n
        exact mul_le_mul_of_nonneg_right (shellCard_le n)
          (shellBound_nonneg f n))
    norm_weight_le_shellBound

/--
Named first-entry shell estimate data for a directly supplied zero-side weight.
-/
structure SchwartzRiemannWeilAbstractFirstEntryShellEstimate
    (exhaustion : ComplexCompactExhaustion) where
  weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  summable_boundTotal :
    forall f : SchwartzLineTestFunction,
      Summable (fun n : Nat => shellCardBound n * shellBound f n)
  norm_weight_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (weight f rho) <= shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilAbstractFirstEntryShellEstimate

/-- Abstract first-entry shell estimates produce an abstract finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate : SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant :=
  exhaustion.toAbstractFiniteShellMajorantOfFirstEntryBounds
    estimate.weight
    estimate.shellCardBound
    estimate.shellBound
    estimate.shellBound_nonneg
    estimate.shellCard_le
    estimate.summable_boundTotal
    estimate.norm_weight_le_shellBound

/-- Abstract first-entry shell estimates give absolute summability of the supplied weight. -/
theorem summable_norm_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate : SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (estimate.weight f rho)) :=
  estimate.toFiniteShellMajorant.summable_norm_weight f

/-- Abstract first-entry shell estimates turn the supplied weight into a zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate : SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toFiniteShellMajorant.toZeroSide

/-- The induced zero side has exactly the supplied abstract weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate : SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = estimate.weight f rho :=
  rfl

/-- Compact-exhaustion sums for abstract first-entry estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate : SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilAbstractFirstEntryShellEstimate

/--
Eventual summable tail majorants for a directly supplied zero-side weight.

After a finite cutoff, the first-entry shell total
`shellCardBound * shellBound` only needs to be dominated by any summable tail.
-/
structure SchwartzRiemannWeilAbstractEventualSummableTailMajorant
    (exhaustion : ComplexCompactExhaustion) where
  weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  tailMajorant : SchwartzLineTestFunction -> Nat -> Real
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  summable_tailMajorant :
    forall f : SchwartzLineTestFunction, Summable (tailMajorant f)
  tail_product_le_majorant :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellCardBound (n + cutoff) * shellBound f (n + cutoff) <=
        tailMajorant f n
  norm_weight_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (weight f rho) <= shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilAbstractEventualSummableTailMajorant

/-- An abstract summable tail majorant makes all first-entry shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) := by
  rw [← @summable_nat_add_iff Real _ _ _ _ estimate.cutoff]
  refine Summable.of_nonneg_of_le
    (f := estimate.tailMajorant f)
    (g := fun n : Nat =>
      estimate.shellCardBound (n + estimate.cutoff) *
        estimate.shellBound f (n + estimate.cutoff)) ?_ ?_
    (estimate.summable_tailMajorant f)
  · intro n
    have hcard_nonneg : 0 <= estimate.shellCardBound (n + estimate.cutoff) :=
      (Nat.cast_nonneg
        (exhaustion.zetaZeroFirstEntryShell (n + estimate.cutoff)).card).trans
        (estimate.shellCard_le (n + estimate.cutoff))
    exact mul_nonneg hcard_nonneg
      (estimate.shellBound_nonneg f (n + estimate.cutoff))
  · intro n
    exact estimate.tail_product_le_majorant f n

/-- Abstract tail majorants produce the named first-entry shell estimate. -/
def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion) :
    SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion where
  weight := estimate.weight
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  summable_boundTotal := estimate.summable_boundTotal
  norm_weight_le_shellBound := estimate.norm_weight_le_shellBound

/-- Abstract tail majorants produce an abstract finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant :=
  estimate.toFirstEntryShellEstimate.toFiniteShellMajorant

/-- Abstract tail majorants give absolute summability of the supplied weight. -/
theorem summable_norm_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (estimate.weight f rho)) :=
  estimate.toFiniteShellMajorant.summable_norm_weight f

/-- Abstract tail majorants turn the supplied weight into a zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toFiniteShellMajorant.toZeroSide

/-- The zero side induced by abstract tail majorants has the supplied weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = estimate.weight f rho :=
  rfl

/-- Compact-exhaustion sums for abstract tail majorants converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilAbstractEventualSummableTailMajorant

/--
Eventual p-series tail majorants for a directly supplied zero-side weight.

This keeps the strongest p-series summability route available when the actual
zero-side weight is obtained from a restricted source construction rather than
from a global extension system.
-/
structure SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant
    (exhaustion : ComplexCompactExhaustion) where
  weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  constant : SchwartzLineTestFunction -> Real
  shift : SchwartzLineTestFunction -> Real
  exponent : SchwartzLineTestFunction -> Real
  constant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= constant f
  one_lt_exponent :
    forall f : SchwartzLineTestFunction, 1 < exponent f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_product_le_pseries :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellCardBound (n + cutoff) * shellBound f (n + cutoff) <=
        constant f * (1 / |(n : Real) + shift f| ^ exponent f)
  norm_weight_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (weight f rho) <= shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant

/-- Abstract p-series tail estimates produce the general summable-tail majorant. -/
noncomputable def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion) :
    SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion where
  weight := estimate.weight
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  tailMajorant := fun f n =>
    estimate.constant f * (1 / |(n : Real) + estimate.shift f| ^
      estimate.exponent f)
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  summable_tailMajorant := fun f =>
    Summable.mul_left (estimate.constant f)
      ((Real.summable_one_div_nat_add_rpow
        (estimate.shift f) (estimate.exponent f)).2
        (estimate.one_lt_exponent f))
  tail_product_le_majorant := estimate.tail_product_le_pseries
  norm_weight_le_shellBound := estimate.norm_weight_le_shellBound

/-- Abstract p-series tail estimates make all first-entry shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) :=
  estimate.toEventualSummableTailMajorant.summable_boundTotal f

/-- Abstract p-series tail estimates produce the named first-entry shell estimate. -/
noncomputable def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion) :
    SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion :=
  estimate.toEventualSummableTailMajorant.toFirstEntryShellEstimate

/-- Abstract p-series tail estimates produce an abstract finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant :=
  estimate.toEventualSummableTailMajorant.toFiniteShellMajorant

/-- Abstract p-series tail estimates give absolute summability of the supplied weight. -/
theorem summable_norm_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (estimate.weight f rho)) :=
  estimate.toFiniteShellMajorant.summable_norm_weight f

/-- Abstract p-series tail estimates turn the supplied weight into a zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toEventualSummableTailMajorant.toZeroSide

/-- Abstract p-series tail estimates make the supplied zero-side weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (estimate.weight f) :=
  estimate.toFiniteShellMajorant.summable_weight f

/-- The zero side induced by abstract p-series tails has the supplied weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = estimate.weight f rho :=
  rfl

/-- Compact-exhaustion sums for abstract p-series tail estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant

/--
Abstract eventual polynomial-cardinality p-series tail majorants.

This is the direct-weight analogue of
`SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant`: shell counts may
grow like `|n + 1| ^ g`, while the supplied zero-side weight is bounded on each
shell by a p-series with decay exponent `exponent f + g`. Lean cancels the
polynomial growth and produces the abstract p-series certificate with exponent
`exponent f`.
-/
structure SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
    (exhaustion : ComplexCompactExhaustion) where
  weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellCardConstant : Real
  growth : Real
  zeroConstant : SchwartzLineTestFunction -> Real
  exponent : SchwartzLineTestFunction -> Real
  shellCardConstant_nonneg : 0 <= shellCardConstant
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  one_lt_exponent :
    forall f : SchwartzLineTestFunction, 1 < exponent f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_shellCardBound_le :
    forall n : Nat,
      shellCardBound (n + cutoff) <=
        shellCardConstant * |(n : Real) + 1| ^ growth
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <=
        zeroConstant f *
          (1 / |(n : Real) + 1| ^ (exponent f + growth))
  norm_weight_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (weight f rho) <= shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant

/-- Polynomial-cardinality direct-weight estimates produce an abstract p-series certificate. -/
noncomputable def toEventualPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion) :
    SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion where
  weight := estimate.weight
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  constant := fun f => estimate.shellCardConstant * estimate.zeroConstant f
  shift := fun _ => 1
  exponent := estimate.exponent
  constant_nonneg := fun f =>
    mul_nonneg estimate.shellCardConstant_nonneg
      (estimate.zeroConstant_nonneg f)
  one_lt_exponent := estimate.one_lt_exponent
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  tail_product_le_pseries := fun f n => by
    let base : Real := |(n : Real) + 1|
    have hbase_pos : 0 < base := by
      dsimp [base]
      positivity
    have hcardMajorant_nonneg :
        0 <= estimate.shellCardConstant * base ^ estimate.growth :=
      mul_nonneg estimate.shellCardConstant_nonneg
        (Real.rpow_nonneg (le_of_lt hbase_pos) estimate.growth)
    calc
      estimate.shellCardBound (n + estimate.cutoff) *
          estimate.shellBound f (n + estimate.cutoff)
          <=
            (estimate.shellCardConstant * base ^ estimate.growth) *
              (estimate.zeroConstant f *
                (1 / base ^ (estimate.exponent f + estimate.growth))) := by
        dsimp [base]
        exact mul_le_mul (estimate.tail_shellCardBound_le n)
          (estimate.tail_shellBound_le f n)
          (estimate.shellBound_nonneg f (n + estimate.cutoff))
          hcardMajorant_nonneg
      _ <=
            (estimate.shellCardConstant * estimate.zeroConstant f) *
              (1 / base ^ estimate.exponent f) := by
        have hsplit :
            base ^ (estimate.exponent f + estimate.growth) =
              base ^ estimate.exponent f * base ^ estimate.growth :=
          Real.rpow_add hbase_pos (estimate.exponent f) estimate.growth
        have hg_ne : base ^ estimate.growth ≠ 0 :=
          (Real.rpow_pos_of_pos hbase_pos estimate.growth).ne'
        have he_ne : base ^ estimate.exponent f ≠ 0 :=
          (Real.rpow_pos_of_pos hbase_pos (estimate.exponent f)).ne'
        rw [hsplit]
        field_simp [hg_ne, he_ne]
        ring_nf
        exact le_rfl
      _ =
            (estimate.shellCardConstant * estimate.zeroConstant f) *
              (1 / |(n : Real) + 1| ^ estimate.exponent f) := by
        rfl
  norm_weight_le_shellBound := estimate.norm_weight_le_shellBound

/-- Polynomial-cardinality estimates produce the abstract summable-tail certificate. -/
noncomputable def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion) :
    SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion :=
  estimate.toEventualPSeriesTailMajorant.toEventualSummableTailMajorant

/-- Polynomial-cardinality estimates make all first-entry shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) :=
  estimate.toEventualPSeriesTailMajorant.summable_boundTotal f

/-- Polynomial-cardinality estimates produce the named abstract shell estimate. -/
noncomputable def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion) :
    SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion :=
  estimate.toEventualPSeriesTailMajorant.toFirstEntryShellEstimate

/-- Polynomial-cardinality estimates produce an abstract finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant :=
  estimate.toEventualPSeriesTailMajorant.toFiniteShellMajorant

/-- Polynomial-cardinality estimates give absolute summability of the supplied weight. -/
theorem summable_norm_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (estimate.weight f rho)) :=
  estimate.toEventualPSeriesTailMajorant.summable_norm_weight f

/-- Polynomial-cardinality estimates turn the supplied weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toEventualPSeriesTailMajorant.toZeroSide

/-- Polynomial-cardinality estimates make the supplied zero-side weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (estimate.weight f) :=
  estimate.toEventualPSeriesTailMajorant.summable_weight f

/-- The zero side induced by polynomial-cardinality estimates has the supplied weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = estimate.weight f rho :=
  rfl

/-- Compact-exhaustion sums for polynomial-cardinality estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant

/--
Abstract eventual polynomial-cardinality decay tail majorants.

This is the most natural direct-weight statement for the restricted-source
p-series route: first-entry shell counts grow like `|n + 1| ^ g`, the supplied
zero-side weight decays like `|n + 1| ^ (-d_f)` on those shells, and
`g + 1 < d_f`. Lean converts the margin into the abstract polynomial-cardinality
p-series certificate by using exponent `d_f - g`.
-/
structure SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
    (exhaustion : ComplexCompactExhaustion) where
  weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellCardConstant : Real
  growth : Real
  zeroConstant : SchwartzLineTestFunction -> Real
  decayExponent : SchwartzLineTestFunction -> Real
  shellCardConstant_nonneg : 0 <= shellCardConstant
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  growth_add_one_lt_decay :
    forall f : SchwartzLineTestFunction, growth + 1 < decayExponent f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_shellCardBound_le :
    forall n : Nat,
      shellCardBound (n + cutoff) <=
        shellCardConstant * |(n : Real) + 1| ^ growth
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <=
        zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f)
  norm_weight_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (weight f rho) <= shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant

/-- Polynomial count plus direct decay margin produces the p-series template. -/
noncomputable def toEventualPolynomialCardPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion) :
    SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
      exhaustion where
  weight := estimate.weight
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  shellCardConstant := estimate.shellCardConstant
  growth := estimate.growth
  zeroConstant := estimate.zeroConstant
  exponent := fun f => estimate.decayExponent f - estimate.growth
  shellCardConstant_nonneg := estimate.shellCardConstant_nonneg
  zeroConstant_nonneg := estimate.zeroConstant_nonneg
  one_lt_exponent := fun f => by
    linarith [estimate.growth_add_one_lt_decay f]
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  tail_shellCardBound_le := estimate.tail_shellCardBound_le
  tail_shellBound_le := fun f n => by
    have hExp :
        estimate.decayExponent f - estimate.growth + estimate.growth =
          estimate.decayExponent f := by
      ring
    simpa [hExp] using estimate.tail_shellBound_le f n
  norm_weight_le_shellBound := estimate.norm_weight_le_shellBound

/-- Polynomial count plus decay estimates produce the abstract p-series certificate. -/
noncomputable def toEventualPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion) :
    SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion :=
  estimate.toEventualPolynomialCardPSeriesTailMajorant.toEventualPSeriesTailMajorant

/-- Polynomial count plus decay estimates produce the abstract summable-tail certificate. -/
noncomputable def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion) :
    SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion :=
  estimate.toEventualPSeriesTailMajorant.toEventualSummableTailMajorant

/-- Polynomial count plus decay estimates make all first-entry shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) :=
  estimate.toEventualPSeriesTailMajorant.summable_boundTotal f

/-- Polynomial count plus decay estimates produce the named abstract shell estimate. -/
noncomputable def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion) :
    SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion :=
  estimate.toEventualPSeriesTailMajorant.toFirstEntryShellEstimate

/-- Polynomial count plus decay estimates produce an abstract finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant :=
  estimate.toEventualPSeriesTailMajorant.toFiniteShellMajorant

/-- Polynomial count plus decay estimates give absolute summability of the supplied weight. -/
theorem summable_norm_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (estimate.weight f rho)) :=
  estimate.toEventualPSeriesTailMajorant.summable_norm_weight f

/-- Polynomial count plus decay estimates turn the supplied weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toEventualPSeriesTailMajorant.toZeroSide

/-- Polynomial count plus decay estimates make the supplied zero-side weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (estimate.weight f) :=
  estimate.toEventualPSeriesTailMajorant.summable_weight f

/-- The zero side induced by polynomial-count decay estimates has the supplied weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = estimate.weight f rho :=
  rfl

/-- Compact-exhaustion sums for polynomial-count decay estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant

namespace SchwartzRiemannWeilEventualSummableTailMajorant

/--
Forget the global extension system in an eventual summable-tail certificate,
keeping only the induced real-valued weight and its abstract shell bound.
-/
noncomputable def toAbstractEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system) :
    SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion where
  weight := system.weight
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  tailMajorant := estimate.tailMajorant
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  summable_tailMajorant := estimate.summable_tailMajorant
  tail_product_le_majorant := estimate.tail_product_le_majorant
  norm_weight_le_shellBound := fun f rho =>
    (system.norm_weight_le_norm_zeroValue f rho).trans
      (estimate.norm_zeroValue_le_shellBound f rho)

end SchwartzRiemannWeilEventualSummableTailMajorant

namespace SchwartzRiemannWeilEventualPSeriesTailMajorant

/--
Forget the global extension system in a p-series certificate, keeping the
extension-induced weight as an abstract zero-side p-series target.
-/
noncomputable def toAbstractEventualPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system) :
    SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion where
  weight := system.weight
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  constant := estimate.constant
  shift := estimate.shift
  exponent := estimate.exponent
  constant_nonneg := estimate.constant_nonneg
  one_lt_exponent := estimate.one_lt_exponent
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  tail_product_le_pseries := estimate.tail_product_le_pseries
  norm_weight_le_shellBound := fun f rho =>
    (system.norm_weight_le_norm_zeroValue f rho).trans
      (estimate.norm_zeroValue_le_shellBound f rho)

end SchwartzRiemannWeilEventualPSeriesTailMajorant

/--
Eventual bounded-cardinality p-series tail majorants.

This is a separated concrete special case: after a finite cutoff, the shell
cardinality bound is uniformly bounded, while the zero contribution has
p-series decay. Lean combines these into the p-series tail certificate above.
-/
structure SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellCardConstant : Real
  zeroConstant : SchwartzLineTestFunction -> Real
  shift : SchwartzLineTestFunction -> Real
  exponent : SchwartzLineTestFunction -> Real
  shellCardConstant_nonneg : 0 <= shellCardConstant
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  one_lt_exponent :
    forall f : SchwartzLineTestFunction, 1 < exponent f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_shellCardBound_le :
    forall n : Nat, shellCardBound (n + cutoff) <= shellCardConstant
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <=
        zeroConstant f * (1 / |(n : Real) + shift f| ^ exponent f)
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant

/-- Bounded-cardinality p-series estimates produce a p-series tail certificate. -/
noncomputable def toEventualPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system where
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  constant := fun f => estimate.shellCardConstant * estimate.zeroConstant f
  shift := estimate.shift
  exponent := estimate.exponent
  constant_nonneg := fun f =>
    mul_nonneg estimate.shellCardConstant_nonneg
      (estimate.zeroConstant_nonneg f)
  one_lt_exponent := estimate.one_lt_exponent
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  tail_product_le_pseries := fun f n => by
    calc
      estimate.shellCardBound (n + estimate.cutoff) *
          estimate.shellBound f (n + estimate.cutoff)
          <= estimate.shellCardConstant *
              (estimate.zeroConstant f *
                (1 / |(n : Real) + estimate.shift f| ^
                  estimate.exponent f)) :=
        mul_le_mul (estimate.tail_shellCardBound_le n)
          (estimate.tail_shellBound_le f n)
          (estimate.shellBound_nonneg f (n + estimate.cutoff))
          estimate.shellCardConstant_nonneg
      _ <=
          (estimate.shellCardConstant * estimate.zeroConstant f) *
            (1 / |(n : Real) + estimate.shift f| ^ estimate.exponent f) := by
        ring_nf
        exact le_rfl
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- Bounded-cardinality p-series estimates produce the summable-tail certificate. -/
noncomputable def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system :=
  estimate.toEventualPSeriesTailMajorant.toEventualSummableTailMajorant

/-- Bounded-cardinality p-series estimates make all shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) :=
  estimate.toEventualPSeriesTailMajorant.summable_boundTotal f

/-- Bounded-cardinality p-series estimates produce the named shell estimate. -/
noncomputable def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system :=
  estimate.toEventualPSeriesTailMajorant.toFirstEntryShellEstimate

/-- Bounded-cardinality p-series estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toEventualPSeriesTailMajorant.toFiniteShellMajorant

/-- Bounded-cardinality p-series estimates induce the norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toEventualPSeriesTailMajorant.toNormMajorant

/-- Bounded-cardinality p-series estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toEventualPSeriesTailMajorant.summable_norm_zeroValue f

/-- Bounded-cardinality p-series estimates give absolute convergence. -/
noncomputable def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toEventualPSeriesTailMajorant.toAbsoluteConvergence

/-- Bounded-cardinality p-series estimates give real-weight summability. -/
noncomputable def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toEventualPSeriesTailMajorant.toWeightSummability

/-- Bounded-cardinality p-series estimates turn the candidate weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- Bounded-cardinality p-series estimates make the extension-induced weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  estimate.toEventualPSeriesTailMajorant.summable_weight f

/-- The zero side induced by bounded-cardinality p-series estimates has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for bounded-cardinality p-series estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant
        exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilEventualBoundedCardPSeriesTailMajorant

/--
Eventual polynomial-cardinality p-series tail majorants.

This concrete separated route allows polynomially growing tail shell counts.
If the shell-cardinality bound grows like `|n + 1| ^ g` and the zero
contribution decays like `|n + 1| ^ -(s_f + g)` with `1 < s_f`, then the shell
totals have p-series exponent `s_f`.
-/
structure SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellCardConstant : Real
  growth : Real
  zeroConstant : SchwartzLineTestFunction -> Real
  exponent : SchwartzLineTestFunction -> Real
  shellCardConstant_nonneg : 0 <= shellCardConstant
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  one_lt_exponent :
    forall f : SchwartzLineTestFunction, 1 < exponent f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_shellCardBound_le :
    forall n : Nat,
      shellCardBound (n + cutoff) <=
        shellCardConstant * |(n : Real) + 1| ^ growth
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <=
        zeroConstant f *
          (1 / |(n : Real) + 1| ^ (exponent f + growth))
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant

/-- Polynomial-cardinality p-series estimates produce a p-series tail certificate. -/
noncomputable def toEventualPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system where
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  constant := fun f => estimate.shellCardConstant * estimate.zeroConstant f
  shift := fun _ => 1
  exponent := estimate.exponent
  constant_nonneg := fun f =>
    mul_nonneg estimate.shellCardConstant_nonneg
      (estimate.zeroConstant_nonneg f)
  one_lt_exponent := estimate.one_lt_exponent
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  tail_product_le_pseries := fun f n => by
    let base : Real := |(n : Real) + 1|
    have hbase_pos : 0 < base := by
      dsimp [base]
      positivity
    have hcardMajorant_nonneg :
        0 <= estimate.shellCardConstant * base ^ estimate.growth :=
      mul_nonneg estimate.shellCardConstant_nonneg
        (Real.rpow_nonneg (le_of_lt hbase_pos) estimate.growth)
    calc
      estimate.shellCardBound (n + estimate.cutoff) *
          estimate.shellBound f (n + estimate.cutoff)
          <=
            (estimate.shellCardConstant * base ^ estimate.growth) *
              (estimate.zeroConstant f *
                (1 / base ^ (estimate.exponent f + estimate.growth))) := by
        dsimp [base]
        exact mul_le_mul (estimate.tail_shellCardBound_le n)
          (estimate.tail_shellBound_le f n)
          (estimate.shellBound_nonneg f (n + estimate.cutoff))
          hcardMajorant_nonneg
      _ <=
            (estimate.shellCardConstant * estimate.zeroConstant f) *
              (1 / base ^ estimate.exponent f) := by
        have hsplit :
            base ^ (estimate.exponent f + estimate.growth) =
              base ^ estimate.exponent f * base ^ estimate.growth :=
          Real.rpow_add hbase_pos (estimate.exponent f) estimate.growth
        have hg_ne : base ^ estimate.growth ≠ 0 :=
          (Real.rpow_pos_of_pos hbase_pos estimate.growth).ne'
        have he_ne : base ^ estimate.exponent f ≠ 0 :=
          (Real.rpow_pos_of_pos hbase_pos (estimate.exponent f)).ne'
        rw [hsplit]
        field_simp [hg_ne, he_ne]
        ring_nf
        exact le_rfl
      _ =
            (estimate.shellCardConstant * estimate.zeroConstant f) *
              (1 / |(n : Real) + 1| ^ estimate.exponent f) := by
        rfl
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- Polynomial-cardinality p-series estimates produce the summable-tail certificate. -/
noncomputable def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system :=
  estimate.toEventualPSeriesTailMajorant.toEventualSummableTailMajorant

/-- Polynomial-cardinality p-series estimates make all shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) :=
  estimate.toEventualPSeriesTailMajorant.summable_boundTotal f

/-- Polynomial-cardinality p-series estimates produce the named shell estimate. -/
noncomputable def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system :=
  estimate.toEventualPSeriesTailMajorant.toFirstEntryShellEstimate

/-- Polynomial-cardinality p-series estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toEventualPSeriesTailMajorant.toFiniteShellMajorant

/-- Polynomial-cardinality p-series estimates induce the norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toEventualPSeriesTailMajorant.toNormMajorant

/-- Polynomial-cardinality p-series estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toEventualPSeriesTailMajorant.summable_norm_zeroValue f

/-- Polynomial-cardinality p-series estimates give absolute convergence. -/
noncomputable def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toEventualPSeriesTailMajorant.toAbsoluteConvergence

/-- Polynomial-cardinality p-series estimates give real-weight summability. -/
noncomputable def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toEventualPSeriesTailMajorant.toWeightSummability

/-- Polynomial-cardinality p-series estimates turn the candidate weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- Polynomial-cardinality p-series estimates make the extension-induced weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  estimate.toEventualPSeriesTailMajorant.summable_weight f

/-- The zero side induced by polynomial-cardinality p-series estimates has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for polynomial-cardinality p-series estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
        exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant

/--
Eventual polynomial-cardinality decay tail majorants.

This is the natural way to state the previous p-series template from analytic
estimates: shell counts grow like `|n + 1| ^ g`, zero contributions decay like
`|n + 1| ^ (-d_f)`, and the decay exponent beats the growth exponent by more
than one.
-/
structure SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  shellCardConstant : Real
  growth : Real
  zeroConstant : SchwartzLineTestFunction -> Real
  decayExponent : SchwartzLineTestFunction -> Real
  shellCardConstant_nonneg : 0 <= shellCardConstant
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  growth_add_one_lt_decay :
    forall f : SchwartzLineTestFunction, growth + 1 < decayExponent f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_shellCardBound_le :
    forall n : Nat,
      shellCardBound (n + cutoff) <=
        shellCardConstant * |(n : Real) + 1| ^ growth
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <=
        zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f)
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant

/-- Polynomial count plus sufficiently strong decay produces the p-series template. -/
noncomputable def toEventualPolynomialCardPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilEventualPolynomialCardPSeriesTailMajorant
      exhaustion system where
  cutoff := estimate.cutoff
  shellCardBound := estimate.shellCardBound
  shellBound := estimate.shellBound
  shellCardConstant := estimate.shellCardConstant
  growth := estimate.growth
  zeroConstant := estimate.zeroConstant
  exponent := fun f => estimate.decayExponent f - estimate.growth
  shellCardConstant_nonneg := estimate.shellCardConstant_nonneg
  zeroConstant_nonneg := estimate.zeroConstant_nonneg
  one_lt_exponent := fun f => by
    linarith [estimate.growth_add_one_lt_decay f]
  shellBound_nonneg := estimate.shellBound_nonneg
  shellCard_le := estimate.shellCard_le
  tail_shellCardBound_le := estimate.tail_shellCardBound_le
  tail_shellBound_le := fun f n => by
    have hExp :
        estimate.decayExponent f - estimate.growth + estimate.growth =
          estimate.decayExponent f := by
      ring
    simpa [hExp] using estimate.tail_shellBound_le f n
  norm_zeroValue_le_shellBound := estimate.norm_zeroValue_le_shellBound

/-- Polynomial count plus decay estimates produce the p-series tail certificate. -/
noncomputable def toEventualPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system :=
  estimate.toEventualPolynomialCardPSeriesTailMajorant.toEventualPSeriesTailMajorant

/-- Polynomial count plus decay estimates produce the summable-tail certificate. -/
noncomputable def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system :=
  estimate.toEventualPSeriesTailMajorant.toEventualSummableTailMajorant

/-- Polynomial count plus decay estimates make all shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.shellCardBound n * estimate.shellBound f n) :=
  estimate.toEventualPSeriesTailMajorant.summable_boundTotal f

/-- Polynomial count plus decay estimates produce the named shell estimate. -/
noncomputable def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system :=
  estimate.toEventualPSeriesTailMajorant.toFirstEntryShellEstimate

/-- Polynomial count plus decay estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toEventualPSeriesTailMajorant.toFiniteShellMajorant

/-- Polynomial count plus decay estimates induce the norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toEventualPSeriesTailMajorant.toNormMajorant

/-- Polynomial count plus decay estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) :=
  estimate.toEventualPSeriesTailMajorant.summable_norm_zeroValue f

/-- Polynomial count plus decay estimates give absolute convergence. -/
noncomputable def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toEventualPSeriesTailMajorant.toAbsoluteConvergence

/-- Polynomial count plus decay estimates give real-weight summability. -/
noncomputable def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toEventualPSeriesTailMajorant.toWeightSummability

/-- Polynomial count plus decay estimates turn the candidate weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- Polynomial count plus decay estimates make the extension-induced weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  estimate.toEventualPSeriesTailMajorant.summable_weight f

/-- The zero side induced by polynomial-count decay estimates has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for polynomial-count decay estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
        exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant

/--
Compact support of the complex zero contribution.

This is a restricted but concrete route into the majorant interface: if, for
each test function, the complex zero contribution vanishes outside a compact
subset of the zero plane, then the induced norm-majorant is summable because
actual zeta zeroes are finite in compact sets.
-/
structure SchwartzRiemannWeilCompactSupportMajorant
    (system : SchwartzRiemannWeilExtensionSystem) where
  support : SchwartzLineTestFunction -> Set Complex
  compact_support :
    forall f : SchwartzLineTestFunction, IsCompact (support f)
  zeroValue_eq_zero_of_not_mem :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      (rho : Complex) ∉ support f -> system.zeroValue f rho = 0

namespace SchwartzRiemannWeilCompactSupportMajorant

/-- Compact support gives a summable norm-majorant. -/
noncomputable def toNormMajorant
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system) :
    SchwartzRiemannWeilNormMajorant system where
  majorant := fun f rho => norm (system.zeroValue f rho)
  summable_majorant := fun f =>
    zetaZeroWeight_summable_of_supportedInCompact
      (certificate.support f)
      (certificate.compact_support f)
      (by
        intro rho hrho
        change norm (system.zeroValue f rho) = 0
        rw [certificate.zeroValue_eq_zero_of_not_mem f rho hrho]
        simp)
  norm_zeroValue_le_majorant := fun _ _ => le_rfl

/-- Compact support gives absolute convergence of the complex zero contribution. -/
def toAbsoluteConvergence
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  certificate.toNormMajorant.toAbsoluteConvergence

/-- Compact support gives summability of the induced real-valued weight. -/
def toWeightSummability
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system) :
    SchwartzRiemannWeilWeightSummability system :=
  certificate.toNormMajorant.toWeightSummability

/-- Compact support turns the candidate weight into the zero-side interface. -/
noncomputable def toZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system) :
    SchwartzRiemannWeilZeroSide :=
  certificate.toWeightSummability.toZeroSide

/-- The zero side induced by compact support has exactly the candidate weight. -/
theorem toZeroSide_weight
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    certificate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for compactly supported candidate weights converge globally. -/
theorem tendsto_windowZeroSide
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => certificate.toZeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (certificate.toZeroSide.zeroSide f)) :=
  certificate.toZeroSide.tendsto_windowZeroSide exhaustion f

end SchwartzRiemannWeilCompactSupportMajorant

end RiemannHypothesisProject
