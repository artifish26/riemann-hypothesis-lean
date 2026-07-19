import RiemannHypothesisProject.GuinandWeilConcrete.ErrorEnvelope

/-!
# Restricted-source wrappers for concrete Guinand-Weil formulae

This module contains restricted source-class theorem wrappers, all-test source
formula wrappers, and endpoint formula-data constructors for the concrete
Guinand-Weil formula route.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

/--
Restricted source-class formula theorem with compact Fourier support.  A future
Paley-Wiener or paper-specific admissible class can use this once it supplies
zero-side summability, the finite signed-error contour identity, and the
decaying error envelope on admissible tests.
-/
theorem guinandWeilConcrete_restrictedSourceFormula_of_truncatedEventualErrorEnvelope_of_fourierCompactSupport
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (hzero :
      forall f : SchwartzLineTestFunction,
        admissible f -> Summable (system.weight f))
    (hfourier :
      forall f : SchwartzLineTestFunction,
        admissible f -> GuinandWeilFourierCompactSupport f)
    (hfinite :
      forall (cutoff : Nat) (f : SchwartzLineTestFunction),
        admissible f ->
          guinandWeilTruncatedZeroSide system
              (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
            guinandWeilTruncatedResidualSide system cutoff f +
              errorSide cutoff f)
    (herror_bound :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ∀ᶠ cutoff : Nat in atTop,
            |errorSide cutoff f| <= errorEnvelope cutoff f)
    (henvelope_zero :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0))
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_truncatedEventualErrorEnvelope_of_fourierCompactSupport
    system exhaustion errorSide errorEnvelope f (hzero f hf) (hfourier f hf)
    (fun cutoff => hfinite cutoff f hf) (herror_bound f hf)
    (henvelope_zero f hf)

/--
Restricted source-class formula theorem with compact support on both sides.
Each admissible test may choose its own compact zero-support window.
-/
theorem guinandWeilConcrete_restrictedSourceFormula_of_truncatedEventualErrorEnvelope_of_compactSupports
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (hzeroSupport :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ∃ K : Set Complex, ∃ _hK : IsCompact K,
            ZetaZeroWeightSupportedInCompact K (system.weight f))
    (hfourier :
      forall f : SchwartzLineTestFunction,
        admissible f -> GuinandWeilFourierCompactSupport f)
    (hfinite :
      forall (cutoff : Nat) (f : SchwartzLineTestFunction),
        admissible f ->
          guinandWeilTruncatedZeroSide system
              (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
            guinandWeilTruncatedResidualSide system cutoff f +
              errorSide cutoff f)
    (herror_bound :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ∀ᶠ cutoff : Nat in atTop,
            |errorSide cutoff f| <= errorEnvelope cutoff f)
    (henvelope_zero :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0))
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f := by
  rcases hzeroSupport f hf with ⟨K, hK, hzeroSupport_f⟩
  exact
    guinandWeilConcrete_sourceFormulaAt_of_truncatedEventualErrorEnvelope_of_compactSupports
      system exhaustion K hK errorSide errorEnvelope f hzeroSupport_f
      (hfourier f hf) (fun cutoff => hfinite cutoff f hf)
      (herror_bound f hf) (henvelope_zero f hf)

/--
Concrete source theorem from a finite signed-error Guinand-Weil formula.

This is the direct source-theorem surface for a borrowed contour-shift proof:
once the proof supplies the finite signed-error identity and the signed error
tends to zero, the checked convergence of the concrete zero/prime/pole/gamma
sides gives the limiting Guinand-Weil identity in the concrete normalization.
-/
theorem guinandWeilConcrete_sourceFormula_of_truncatedError
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (hzero :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hprime :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror :
      forall f : SchwartzLineTestFunction,
        Tendsto (fun cutoff : Nat => errorSide cutoff f) atTop (𝓝 0))
    (f : SchwartzLineTestFunction) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f := by
  have hzero_limit :=
    tendsto_guinandWeilTruncatedZeroSide system exhaustion f (hzero f)
  have hzero_as_residual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (𝓝 (guinandWeilZeroSide system f)) :=
    hzero_limit.congr'
      (Eventually.of_forall fun cutoff => hfinite cutoff f)
  have hresidual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (𝓝 (guinandWeilResidualSide system f + 0)) :=
    (tendsto_guinandWeilTruncatedResidualSide system f (hprime f)).add
      (herror f)
  have hlimit :
      guinandWeilZeroSide system f = guinandWeilResidualSide system f + 0 :=
    tendsto_nhds_unique hzero_as_residual_error hresidual_error
  simpa using hlimit

/--
Concrete source theorem from an eventual absolute error envelope.

This is the common published-proof shape: the contour-shift proof gives a
finite signed error and an eventual absolute bound by an envelope tending to
zero. Lean derives signed-error convergence and then applies the concrete
source theorem above.
-/
theorem guinandWeilConcrete_sourceFormula_of_truncatedEventualErrorEnvelope
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (hzero :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hprime :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror_bound :
      forall f : SchwartzLineTestFunction,
        ∀ᶠ cutoff : Nat in atTop,
          |errorSide cutoff f| <= errorEnvelope cutoff f)
    (henvelope_zero :
      forall f : SchwartzLineTestFunction,
        Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0))
    (f : SchwartzLineTestFunction) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormula_of_truncatedError
    system exhaustion errorSide hzero hprime hfinite
    (fun f => by
      have habs :
          Tendsto (fun cutoff : Nat => |errorSide cutoff f|)
            atTop (𝓝 0) :=
        squeeze_zero'
          (Eventually.of_forall
            (fun cutoff : Nat => abs_nonneg (errorSide cutoff f)))
          (herror_bound f)
          (henvelope_zero f)
      exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs)
    f

/--
Completed-zeta normalized source theorem from a finite signed-error
Guinand-Weil formula.

This is the course-corrected source-formula target: the finite contour identity
is stated with the normalized zero side, so project-known trivial zero
contributions are already assigned to the completed-zeta residual
normalization.
-/
theorem guinandWeilCompletedZetaNormalized_sourceFormula_of_truncatedError
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (hzero :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (hprime :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilCompletedZetaNormalizedFiniteCutoffIdentityWithError system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror :
      forall f : SchwartzLineTestFunction,
        Tendsto (fun cutoff : Nat => errorSide cutoff f) atTop (nhds 0))
    (f : SchwartzLineTestFunction) :
    guinandWeilCompletedZetaNormalizedZeroSide system f =
      guinandWeilResidualSide system f := by
  have hzero_limit :=
    tendsto_guinandWeilTruncatedCompletedZetaNormalizedZeroSide
      system exhaustion f (hzero f)
  have hzero_as_residual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (nhds (guinandWeilCompletedZetaNormalizedZeroSide system f)) :=
    hzero_limit.congr'
      (Eventually.of_forall fun cutoff => hfinite cutoff f)
  have hresidual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (nhds (guinandWeilResidualSide system f + 0)) :=
    (tendsto_guinandWeilTruncatedResidualSide system f (hprime f)).add
      (herror f)
  have hlimit :
      guinandWeilCompletedZetaNormalizedZeroSide system f =
        guinandWeilResidualSide system f + 0 :=
    tendsto_nhds_unique hzero_as_residual_error hresidual_error
  simpa using hlimit

/--
Completed-zeta normalized source theorem from an eventual absolute error
envelope.

The remaining analytic inputs are exactly the borrowed normalized finite
contour identity and a decaying contour-error envelope.
-/
theorem guinandWeilCompletedZetaNormalized_sourceFormula_of_truncatedEventualErrorEnvelope
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (hzero :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (hprime :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilCompletedZetaNormalizedFiniteCutoffIdentityWithError system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror_bound :
      forall f : SchwartzLineTestFunction,
        Filter.Eventually
          (fun cutoff : Nat =>
            |errorSide cutoff f| <= errorEnvelope cutoff f) atTop)
    (henvelope_zero :
      forall f : SchwartzLineTestFunction,
        Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (nhds 0))
    (f : SchwartzLineTestFunction) :
    guinandWeilCompletedZetaNormalizedZeroSide system f =
      guinandWeilResidualSide system f :=
  guinandWeilCompletedZetaNormalized_sourceFormula_of_truncatedError
    system exhaustion errorSide hzero hprime hfinite
    (fun f => by
      have habs :
          Tendsto (fun cutoff : Nat => |errorSide cutoff f|)
            atTop (nhds 0) :=
        squeeze_zero'
          (Eventually.of_forall
            (fun cutoff : Nat => abs_nonneg (errorSide cutoff f)))
          (herror_bound f)
          (henvelope_zero f)
      exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs)
    f

/--
A raw concrete source formula transfers to the completed-zeta normalized source
formula when the raw trivial-zero weights already vanish.
-/
theorem guinandWeilCompletedZetaNormalized_sourceFormula_of_sourceFormula_of_trivialWeight_eq_zero
    (system : SchwartzRiemannWeilExtensionSystem)
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f)
    (htrivial_weight :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) -> system.weight f rho = 0)
    (f : SchwartzLineTestFunction) :
    guinandWeilCompletedZetaNormalizedZeroSide system f =
      guinandWeilResidualSide system f := by
  rw [
    guinandWeilCompletedZetaNormalizedZeroSide_eq_zeroSide_of_trivialWeight_eq_zero
      system f (htrivial_weight f)]
  exact hformula f

/--
A raw concrete source formula transfers to the completed-zeta normalized source
formula under the analytic trivial-zero extension-vanishing normalization.
-/
theorem guinandWeilCompletedZetaNormalized_sourceFormula_of_sourceFormula_of_trivialZeroArgument_extension_eq_zero
    (system : SchwartzRiemannWeilExtensionSystem)
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f)
    (htrivial_extension :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) ->
            system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0)
    (f : SchwartzLineTestFunction) :
    guinandWeilCompletedZetaNormalizedZeroSide system f =
      guinandWeilResidualSide system f :=
  guinandWeilCompletedZetaNormalized_sourceFormula_of_sourceFormula_of_trivialWeight_eq_zero
    system hformula
    (system.trivial_weight_eq_zero_of_trivial_zeroArgument_extension_eq_zero
      htrivial_extension)
    f

/--
A raw finite signed-error contour identity transfers to the completed-zeta
normalized finite identity when the raw trivial-zero weights vanish at every
test function.
-/
theorem GuinandWeilConcreteFiniteCutoffIdentityWithError.to_completedZetaNormalized
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (cutoff : Nat)
    (hfinite :
      GuinandWeilConcreteFiniteCutoffIdentityWithError
        system zeroWindow errorSide cutoff)
    (htrivial_weight :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) -> system.weight f rho = 0) :
    GuinandWeilCompletedZetaNormalizedFiniteCutoffIdentityWithError
      system zeroWindow errorSide cutoff := by
  intro f
  rw [
    guinandWeilTruncatedCompletedZetaNormalizedZeroSide_eq_truncatedZeroSide_of_trivialWeight_eq_zero
      system zeroWindow cutoff f (htrivial_weight f)]
  exact hfinite f

/--
A raw finite signed-error theorem plus trivial-zero weight vanishing yields the
completed-zeta normalized source formula.
-/
theorem guinandWeilCompletedZetaNormalized_sourceFormula_of_truncatedError_of_rawFiniteIdentity
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (hzero :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (hprime :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (htrivial_weight :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) -> system.weight f rho = 0)
    (herror :
      forall f : SchwartzLineTestFunction,
        Tendsto (fun cutoff : Nat => errorSide cutoff f) atTop (nhds 0))
    (f : SchwartzLineTestFunction) :
    guinandWeilCompletedZetaNormalizedZeroSide system f =
      guinandWeilResidualSide system f :=
  guinandWeilCompletedZetaNormalized_sourceFormula_of_truncatedError
    system exhaustion errorSide hzero hprime
    (fun cutoff =>
      (hfinite cutoff).to_completedZetaNormalized
        system (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff
        (htrivial_weight := htrivial_weight))
    herror f

/--
A raw finite signed-error theorem plus analytic trivial-zero extension
vanishing yields the completed-zeta normalized source formula.
-/
theorem guinandWeilCompletedZetaNormalized_sourceFormula_of_truncatedError_of_rawFiniteIdentity_of_trivialZeroArgument_extension_eq_zero
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (hzero :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (hprime :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (htrivial_extension :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) ->
            system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0)
    (herror :
      forall f : SchwartzLineTestFunction,
        Tendsto (fun cutoff : Nat => errorSide cutoff f) atTop (nhds 0))
    (f : SchwartzLineTestFunction) :
    guinandWeilCompletedZetaNormalizedZeroSide system f =
      guinandWeilResidualSide system f :=
  guinandWeilCompletedZetaNormalized_sourceFormula_of_truncatedError_of_rawFiniteIdentity
    system exhaustion errorSide hzero hprime hfinite
    (system.trivial_weight_eq_zero_of_trivial_zeroArgument_extension_eq_zero
      htrivial_extension)
    herror f

/--
The concrete eventual-error source theorem, transported through the checked
componentwise normalization bridge, yields project formula identity data.
-/
def guinandWeilConcreteFormulaData_of_truncatedEventualErrorEnvelope
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (hzero :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hprime :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror_bound :
      forall f : SchwartzLineTestFunction,
        ∀ᶠ cutoff : Nat in atTop,
          |errorSide cutoff f| <= errorEnvelope cutoff f)
    (henvelope_zero :
      forall f : SchwartzLineTestFunction,
        Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0)) :
    SchwartzRiemannWeilFormulaIdentityData (system.toZeroSide hzero) :=
  guinandWeilConcreteFormulaData system hzero
    (guinandWeilConcrete_sourceFormula_of_truncatedEventualErrorEnvelope
      system exhaustion errorSide errorEnvelope hzero hprime hfinite
      herror_bound henvelope_zero)

/--
The completed-zeta normalized eventual-error source theorem, transported
through the checked componentwise normalization bridge, yields project formula
identity data for the normalized zero-side interface.
-/
def guinandWeilCompletedZetaNormalizedFormulaData_of_truncatedEventualErrorEnvelope
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (hzero :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (hprime :
      forall f : SchwartzLineTestFunction,
        Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilCompletedZetaNormalizedFiniteCutoffIdentityWithError system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror_bound :
      forall f : SchwartzLineTestFunction,
        Filter.Eventually
          (fun cutoff : Nat =>
            |errorSide cutoff f| <= errorEnvelope cutoff f) atTop)
    (henvelope_zero :
      forall f : SchwartzLineTestFunction,
        Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (nhds 0)) :
    SchwartzRiemannWeilFormulaIdentityData
      (system.toCompletedZetaNormalizedZeroSide hzero) :=
  guinandWeilCompletedZetaNormalizedFormulaData system hzero
    (guinandWeilCompletedZetaNormalized_sourceFormula_of_truncatedEventualErrorEnvelope
      system exhaustion errorSide errorEnvelope hzero hprime hfinite
      herror_bound henvelope_zero)

end

end RiemannHypothesisProject
