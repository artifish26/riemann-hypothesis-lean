import RiemannHypothesisProject.GuinandWeilConcrete.ResidualCutoff
import RiemannHypothesisProject.GuinandWeilConcrete.ZeroCutoff

/-!
# Formula-gap wrappers for concrete Guinand-Weil formulae

This module contains finite-cutoff signed-error equivalences, formula-error
convergence, side-eventual equality wrappers, and compact-support formula-gap
bounds for the concrete Guinand-Weil formula route.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

/-- The signed-error target is equivalent to identifying the concrete error. -/
theorem GuinandWeilConcreteFiniteCutoffIdentityWithError_iff
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (cutoff : Nat) :
    GuinandWeilConcreteFiniteCutoffIdentityWithError system zeroWindow errorSide cutoff <->
      forall f : SchwartzLineTestFunction,
        guinandWeilConcreteFormulaError system zeroWindow cutoff f =
          errorSide cutoff f := by
  constructor
  · intro h f
    unfold guinandWeilConcreteFormulaError
    rw [h f]
    ring
  · intro h f
    rw [← h f]
    unfold guinandWeilConcreteFormulaError
    ring

/-- Exact cutoff identities are the zero-error special case. -/
theorem GuinandWeilConcreteFiniteCutoffIdentityWithError_zero_iff
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (cutoff : Nat) :
    GuinandWeilConcreteFiniteCutoffIdentityWithError
        system zeroWindow (fun _ _ => 0) cutoff <->
      GuinandWeilConcreteFiniteCutoffIdentity system zeroWindow cutoff := by
  constructor
  · intro h f
    have hf := h f
    simpa [GuinandWeilConcreteFiniteCutoffIdentity,
      GuinandWeilConcreteFiniteCutoffIdentityWithError] using hf
  · intro h f
    have hf := h f
    rw [hf]
    ring

/--
If the limiting concrete formula holds and the zero/prime components are
summable, the actual finite-cutoff formula error tends to zero.
-/
theorem tendsto_guinandWeilConcreteFormulaError_zero
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    (hzero : Summable (system.weight f))
    (hprime : Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hformula :
      guinandWeilZeroSide system f = guinandWeilResidualSide system f) :
    Tendsto
      (fun cutoff : Nat =>
        guinandWeilConcreteFormulaError system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f)
      atTop (𝓝 0) := by
  have hz := tendsto_guinandWeilTruncatedZeroSide system exhaustion f hzero
  have hr := tendsto_guinandWeilTruncatedResidualSide system f hprime
  simpa [guinandWeilConcreteFormulaError, hformula] using hz.sub hr

/--
The same analytic convergence gives an eventual absolute error bound by any
positive constant envelope.
-/
theorem eventually_abs_guinandWeilConcreteFormulaError_le_const
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    (hzero : Summable (system.weight f))
    (hprime : Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hformula :
      guinandWeilZeroSide system f = guinandWeilResidualSide system f)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ cutoff : Nat in atTop,
      |guinandWeilConcreteFormulaError system
        (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f| <= epsilon := by
  have herror :=
    tendsto_guinandWeilConcreteFormulaError_zero system exhaustion f hzero hprime hformula
  have hball :
      Metric.ball (0 : Real) epsilon ∈ 𝓝 (0 : Real) :=
    Metric.ball_mem_nhds (0 : Real) hepsilon
  filter_upwards [herror.eventually hball] with cutoff hcutoff
  exact le_of_lt (by
    simpa [Metric.mem_ball, Real.dist_eq] using hcutoff)

/--
Once the zero and residual cutoffs are exactly stabilized, the concrete
finite-cutoff formula error is eventually the fixed limiting formula gap.
-/
theorem eventually_guinandWeilConcreteFormulaError_eq_formulaGap_of_sidesEventuallyEq
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (f : SchwartzLineTestFunction)
    (hzeroSide :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedZeroSide system zeroWindow cutoff f =
          guinandWeilZeroSide system f)
    (hresidual :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedResidualSide system cutoff f =
          guinandWeilResidualSide system f) :
    ∀ᶠ cutoff : Nat in atTop,
      guinandWeilConcreteFormulaError system zeroWindow cutoff f =
        guinandWeilZeroSide system f - guinandWeilResidualSide system f := by
  filter_upwards [hzeroSide, hresidual] with cutoff hzero hresidual_cutoff
  simp [guinandWeilConcreteFormulaError, hzero, hresidual_cutoff]

/--
Under an exact finite signed-error identity, eventual stabilization of both
cutoff sides forces the signed contour error itself to be the limiting formula
gap.  This is the compact-support obstruction the real error estimate must
kill.
-/
theorem eventually_guinandWeilConcreteErrorSide_eq_formulaGap_of_sidesEventuallyEq
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzeroSide :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedZeroSide system zeroWindow cutoff f =
          guinandWeilZeroSide system f)
    (hresidual :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedResidualSide system cutoff f =
          guinandWeilResidualSide system f)
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError
          system zeroWindow errorSide cutoff) :
    ∀ᶠ cutoff : Nat in atTop,
      errorSide cutoff f =
        guinandWeilZeroSide system f - guinandWeilResidualSide system f := by
  have hformulaError :=
    eventually_guinandWeilConcreteFormulaError_eq_formulaGap_of_sidesEventuallyEq
      system zeroWindow f hzeroSide hresidual
  filter_upwards [hformulaError] with cutoff hgap
  have herror :
      guinandWeilConcreteFormulaError system zeroWindow cutoff f =
        errorSide cutoff f :=
    (GuinandWeilConcreteFiniteCutoffIdentityWithError_iff
      system zeroWindow errorSide cutoff).1 (hfinite cutoff) f
  exact herror.symm.trans hgap

/--
The finite signed-error identity plus exact cutoff stabilization turns an
eventual contour-error envelope into an eventual envelope for the limiting
formula gap itself.
-/
theorem eventually_abs_guinandWeilConcreteFormulaGap_le_errorEnvelope_of_sidesEventuallyEq
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzeroSide :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedZeroSide system zeroWindow cutoff f =
          guinandWeilZeroSide system f)
    (hresidual :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedResidualSide system cutoff f =
          guinandWeilResidualSide system f)
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError
          system zeroWindow errorSide cutoff)
    (herror_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |errorSide cutoff f| <= errorEnvelope cutoff f) :
    ∀ᶠ cutoff : Nat in atTop,
      |guinandWeilZeroSide system f - guinandWeilResidualSide system f| <=
        errorEnvelope cutoff f := by
  have hgap :=
    eventually_guinandWeilConcreteErrorSide_eq_formulaGap_of_sidesEventuallyEq
      system zeroWindow errorSide f hzeroSide hresidual hfinite
  filter_upwards [hgap, herror_bound] with cutoff herror_eq hbound
  simpa [herror_eq] using hbound

/--
At a single cutoff, exact stabilization of the zero and residual sides turns the
finite signed-error identity into a bound for the fixed limiting formula gap.
-/
theorem abs_guinandWeilConcreteFormulaGap_le_errorEnvelope_of_cutoffEq
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (cutoff : Nat)
    (hzeroSide :
      guinandWeilTruncatedZeroSide system zeroWindow cutoff f =
        guinandWeilZeroSide system f)
    (hresidual :
      guinandWeilTruncatedResidualSide system cutoff f =
        guinandWeilResidualSide system f)
    (hfinite :
      GuinandWeilConcreteFiniteCutoffIdentityWithError
        system zeroWindow errorSide cutoff)
    (herror_bound :
      |errorSide cutoff f| <= errorEnvelope cutoff f) :
    |guinandWeilZeroSide system f - guinandWeilResidualSide system f| <=
      errorEnvelope cutoff f := by
  have hformulaError :
      guinandWeilConcreteFormulaError system zeroWindow cutoff f =
        guinandWeilZeroSide system f - guinandWeilResidualSide system f := by
    simp [guinandWeilConcreteFormulaError, hzeroSide, hresidual]
  have herror :
      guinandWeilConcreteFormulaError system zeroWindow cutoff f =
        errorSide cutoff f :=
    (GuinandWeilConcreteFiniteCutoffIdentityWithError_iff
      system zeroWindow errorSide cutoff).1 hfinite f
  have hgap :
      errorSide cutoff f =
        guinandWeilZeroSide system f - guinandWeilResidualSide system f :=
    herror.symm.trans hformulaError
  simpa [hgap] using herror_bound

/--
Concrete pointwise formula-gap bound from source-side compact zero support and
an explicit Fourier support radius.  The only finite-cutoff inputs are that the
zero window contains the compact support and `exp R < cutoff + 1`.
-/
theorem abs_guinandWeilConcreteFormulaGap_le_errorEnvelope_of_compactZeroSupport_fourierSupportRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (cutoff : Nat)
    (hzeroSupport : ZetaZeroWeightSupportedInCompact K (system.weight f))
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (hzeroSubset :
      compactZetaZeroSubtypeFinset K hK ⊆
        exhaustion.zetaZeroSubtypeFinset cutoff)
    (hfourierCutoff : Real.exp R < ((cutoff + 1 : Nat) : Real))
    (hfinite :
      GuinandWeilConcreteFiniteCutoffIdentityWithError
        system (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror_bound :
      |errorSide cutoff f| <= errorEnvelope cutoff f) :
    |guinandWeilZeroSide system f - guinandWeilResidualSide system f| <=
      errorEnvelope cutoff f :=
  abs_guinandWeilConcreteFormulaGap_le_errorEnvelope_of_cutoffEq
    system (fun n => exhaustion.zetaZeroSubtypeFinset n)
    errorSide errorEnvelope f cutoff
    (guinandWeilTruncatedZeroSide_eq_zeroSide_of_supportedInCompact_of_subset
      system exhaustion K hK f hzeroSupport cutoff hzeroSubset)
    (guinandWeilTruncatedResidualSide_eq_residualSide_of_fourierSupportRadius_exp_lt_succ
      system f hR_nonneg hsupport cutoff hfourierCutoff)
    hfinite herror_bound

end

end RiemannHypothesisProject
