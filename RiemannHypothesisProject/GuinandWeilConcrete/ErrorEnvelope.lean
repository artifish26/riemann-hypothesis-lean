import RiemannHypothesisProject.GuinandWeilConcrete.FormulaGap

/-!
# Error-envelope routes for concrete Guinand-Weil formulae

This module contains signed-error, bounded-error, eventual-error, and
inverse-polynomial envelope routes from finite concrete Guinand-Weil cutoff
identities to pointwise source formula identities.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

/--
Epsilon-form contour estimate for the compact-support source class.  If every
positive tolerance admits a cutoff whose zero window contains the compact zero
support, whose prime cutoff clears the Fourier support radius, and whose
signed contour error is below that tolerance, then the limiting concrete
Guinand-Weil formula follows.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_arbitrarilySmallContourError_of_compactZeroSupport_fourierSupportRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzeroSupport : ZetaZeroWeightSupportedInCompact K (system.weight f))
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError
          system (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror_small :
      ∀ epsilon : Real, 0 < epsilon ->
        ∃ cutoff : Nat,
          compactZetaZeroSubtypeFinset K hK ⊆
              exhaustion.zetaZeroSubtypeFinset cutoff ∧
            Real.exp R < ((cutoff + 1 : Nat) : Real) ∧
            |errorSide cutoff f| <= epsilon) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f := by
  have hgap_le :
      ∀ epsilon : Real, 0 < epsilon ->
        |guinandWeilZeroSide system f - guinandWeilResidualSide system f| <=
          epsilon := by
    intro epsilon hepsilon
    rcases herror_small epsilon hepsilon with
      ⟨cutoff, hzeroSubset, hfourierCutoff, herror_bound⟩
    exact
      abs_guinandWeilConcreteFormulaGap_le_errorEnvelope_of_compactZeroSupport_fourierSupportRadius
        system exhaustion K hK errorSide (fun _ _ => epsilon) f cutoff
        hzeroSupport hR_nonneg hsupport hzeroSubset hfourierCutoff
        (hfinite cutoff) herror_bound
  have hgap_abs_zero :
      |guinandWeilZeroSide system f - guinandWeilResidualSide system f| = 0 := by
    by_contra hne
    have hgap_pos :
        0 <
          |guinandWeilZeroSide system f - guinandWeilResidualSide system f| := by
      exact lt_of_le_of_ne
        (abs_nonneg
          (guinandWeilZeroSide system f - guinandWeilResidualSide system f))
        (Ne.symm hne)
    have hhalf :=
      hgap_le
        (|guinandWeilZeroSide system f - guinandWeilResidualSide system f| / 2)
        (half_pos hgap_pos)
    linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hgap_abs_zero)

/--
Tail-convergence form of the compact-support contour estimate.  If the signed
contour error tends to zero along all cutoffs, then sufficiently large cutoffs
can be chosen to satisfy the compact zero-window and Fourier-radius conditions
simultaneously, so the limiting concrete Guinand-Weil formula follows.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_contourError_tendsto_zero_of_compactZeroSupport_fourierSupportRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzeroSupport : ZetaZeroWeightSupportedInCompact K (system.weight f))
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError
          system (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror_zero :
      Tendsto (fun cutoff : Nat => errorSide cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_arbitrarilySmallContourError_of_compactZeroSupport_fourierSupportRadius
    system exhaustion K hK errorSide f hzeroSupport hR_nonneg hsupport hfinite
    (fun epsilon hepsilon => by
      have hzeroSubset :
          ∀ᶠ cutoff : Nat in atTop,
            compactZetaZeroSubtypeFinset K hK ⊆
              exhaustion.zetaZeroSubtypeFinset cutoff :=
        eventually_compactZetaZeroSubtypeFinset_subset_zetaZeroSubtypeFinset
          exhaustion K hK
      have hfourierCutoff :
          ∀ᶠ cutoff : Nat in atTop,
            Real.exp R < ((cutoff + 1 : Nat) : Real) :=
        eventually_fourierSupportRadius_exp_lt_succ R
      have herror_small :
          ∀ᶠ cutoff : Nat in atTop, |errorSide cutoff f| <= epsilon := by
        have hball :
            Metric.ball (0 : Real) epsilon ∈ 𝓝 (0 : Real) :=
          Metric.ball_mem_nhds (0 : Real) hepsilon
        filter_upwards [herror_zero.eventually hball] with cutoff hcutoff
        exact le_of_lt (by
          simpa [Metric.mem_ball, Real.dist_eq] using hcutoff)
      have hcombined :
          ∀ᶠ cutoff : Nat in atTop,
            compactZetaZeroSubtypeFinset K hK ⊆
                exhaustion.zetaZeroSubtypeFinset cutoff ∧
              Real.exp R < ((cutoff + 1 : Nat) : Real) ∧
              |errorSide cutoff f| <= epsilon := by
        filter_upwards [hzeroSubset, hfourierCutoff, herror_small] with
          cutoff hzeroSubset_cutoff hfourierCutoff_cutoff herror_cutoff
        exact ⟨hzeroSubset_cutoff, hfourierCutoff_cutoff, herror_cutoff⟩
      rcases eventually_atTop.1 hcombined with ⟨cutoff, hcutoff⟩
      exact ⟨cutoff, hcutoff cutoff le_rfl⟩)

/--
Compact zero support and an explicit Fourier support radius turn an
inverse-polynomial contour-error estimate into an eventual bound for the final
formula gap, with the cutoff containment and Fourier clearance discharged by
the concrete exhaustion estimates.
-/
theorem eventually_abs_guinandWeilConcreteFormulaGap_le_inversePolynomial_of_compactZeroSupport_fourierSupportRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (constant : SchwartzLineTestFunction -> Real)
    {exponent : Real}
    (f : SchwartzLineTestFunction)
    (hzeroSupport : ZetaZeroWeightSupportedInCompact K (system.weight f))
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError
          system (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |errorSide cutoff f| <=
          constant f * (1 / |(cutoff : Real) + 1| ^ exponent)) :
    ∀ᶠ cutoff : Nat in atTop,
      |guinandWeilZeroSide system f - guinandWeilResidualSide system f| <=
        constant f * (1 / |(cutoff : Real) + 1| ^ exponent) := by
  have hzeroSubset :
      ∀ᶠ cutoff : Nat in atTop,
        compactZetaZeroSubtypeFinset K hK ⊆
          exhaustion.zetaZeroSubtypeFinset cutoff :=
    eventually_compactZetaZeroSubtypeFinset_subset_zetaZeroSubtypeFinset
      exhaustion K hK
  have hfourierCutoff :
      ∀ᶠ cutoff : Nat in atTop,
        Real.exp R < ((cutoff + 1 : Nat) : Real) :=
    eventually_fourierSupportRadius_exp_lt_succ R
  filter_upwards [hzeroSubset, hfourierCutoff, herror_bound] with
    cutoff hzeroSubset_cutoff hfourierCutoff_cutoff hbound
  exact
    abs_guinandWeilConcreteFormulaGap_le_errorEnvelope_of_compactZeroSupport_fourierSupportRadius
      system exhaustion K hK errorSide
      (fun cutoff f =>
        constant f * (1 / |(cutoff : Real) + 1| ^ exponent))
      f cutoff hzeroSupport hR_nonneg hsupport hzeroSubset_cutoff
      hfourierCutoff_cutoff (hfinite cutoff) hbound

/--
A decaying eventual envelope for the fixed limiting formula gap forces the
limiting concrete Guinand-Weil formula identity.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_formulaGapEventualEnvelope
    (system : SchwartzRiemannWeilExtensionSystem)
    (errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hgap_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |guinandWeilZeroSide system f - guinandWeilResidualSide system f| <=
          errorEnvelope cutoff f)
    (henvelope_zero :
      Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f := by
  have hgap_abs :
      Tendsto
        (fun _ : Nat =>
          |guinandWeilZeroSide system f - guinandWeilResidualSide system f|)
        atTop (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall fun _ : Nat =>
        abs_nonneg (guinandWeilZeroSide system f - guinandWeilResidualSide system f))
      hgap_bound
      henvelope_zero
  have hgap_const :
      Tendsto
        (fun _ : Nat =>
          |guinandWeilZeroSide system f - guinandWeilResidualSide system f|)
        atTop
        (𝓝 |guinandWeilZeroSide system f - guinandWeilResidualSide system f|) :=
    tendsto_const_nhds
  have hgap_abs_zero :
      |guinandWeilZeroSide system f - guinandWeilResidualSide system f| = 0 :=
    tendsto_nhds_unique hgap_const hgap_abs
  exact sub_eq_zero.mp (abs_eq_zero.mp hgap_abs_zero)

/--
The inverse-polynomial envelope shape used by contour estimates tends to zero
for every positive exponent.
-/
theorem tendsto_guinandWeilInversePolynomialErrorEnvelope_zero
    (constant : SchwartzLineTestFunction -> Real)
    {exponent : Real} (hexponent : 0 < exponent)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun cutoff : Nat =>
        constant f * (1 / |(cutoff : Real) + 1| ^ exponent))
      atTop (𝓝 0) := by
  have hnat :
      Tendsto (fun cutoff : Nat => (cutoff : Real) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1
      tendsto_natCast_atTop_atTop
  have hpow :
      Tendsto
        (fun cutoff : Nat => ((cutoff : Real) + 1) ^ (-exponent))
        atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_rpow_neg_atTop hexponent).comp hnat
  have htail :
      Tendsto
        (fun cutoff : Nat => 1 / |(cutoff : Real) + 1| ^ exponent)
        atTop (𝓝 0) :=
    hpow.congr' (Eventually.of_forall fun cutoff => by
      have hnonneg : 0 <= (cutoff : Real) + 1 := by positivity
      calc
        ((cutoff : Real) + 1) ^ (-exponent)
            = (((cutoff : Real) + 1) ^ exponent)⁻¹ := by
              rw [Real.rpow_neg hnonneg exponent]
        _ = 1 / |(cutoff : Real) + 1| ^ exponent := by
              rw [abs_of_nonneg hnonneg]
              simp [one_div])
  simpa using (tendsto_const_nhds.mul htail : Tendsto
    (fun cutoff : Nat =>
      constant f * (1 / |(cutoff : Real) + 1| ^ exponent))
    atTop (𝓝 (constant f * 0)))

/--
A finite signed-error contour identity with exact side stabilization is enough
once the remaining contour error is bounded by an inverse-polynomial envelope.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_inversePolynomialErrorEnvelope_of_sidesEventuallyEq
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (constant : SchwartzLineTestFunction -> Real)
    {exponent : Real} (hexponent : 0 < exponent)
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
        |errorSide cutoff f| <=
          constant f * (1 / |(cutoff : Real) + 1| ^ exponent)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_formulaGapEventualEnvelope
    system
    (fun cutoff f =>
      constant f * (1 / |(cutoff : Real) + 1| ^ exponent))
    f
    (eventually_abs_guinandWeilConcreteFormulaGap_le_errorEnvelope_of_sidesEventuallyEq
      system zeroWindow errorSide
      (fun cutoff f =>
        constant f * (1 / |(cutoff : Real) + 1| ^ exponent))
      f hzeroSide hresidual hfinite herror_bound)
    (tendsto_guinandWeilInversePolynomialErrorEnvelope_zero
      constant hexponent f)

/--
Source-class inverse-polynomial formula theorem with concrete compact zero
support and explicit Fourier support radius.  The side stabilization hypotheses
are discharged by the finite zero-window containment and Fourier-radius cutoff
estimates, so the remaining analytic inputs are exactly the finite contour
identity and its inverse-polynomial error bound.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_inversePolynomialErrorEnvelope_of_compactZeroSupport_fourierSupportRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (constant : SchwartzLineTestFunction -> Real)
    {exponent : Real} (hexponent : 0 < exponent)
    (f : SchwartzLineTestFunction)
    (hzeroSupport : ZetaZeroWeightSupportedInCompact K (system.weight f))
    {R : Real} (hR_nonneg : 0 <= R)
    (hsupport :
      ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0)
    (hfinite :
      forall cutoff : Nat,
        GuinandWeilConcreteFiniteCutoffIdentityWithError
          system (fun n => exhaustion.zetaZeroSubtypeFinset n) errorSide cutoff)
    (herror_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |errorSide cutoff f| <=
          constant f * (1 / |(cutoff : Real) + 1| ^ exponent)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_formulaGapEventualEnvelope
    system
    (fun cutoff f =>
      constant f * (1 / |(cutoff : Real) + 1| ^ exponent))
    f
    (eventually_abs_guinandWeilConcreteFormulaGap_le_inversePolynomial_of_compactZeroSupport_fourierSupportRadius
      system exhaustion K hK errorSide constant f hzeroSupport
      hR_nonneg hsupport hfinite herror_bound)
    (tendsto_guinandWeilInversePolynomialErrorEnvelope_zero
      constant hexponent f)

/--
Pointwise concrete source theorem from a finite signed-error Guinand-Weil
formula.  This is the source-class version of the limiting argument: all
analytic hypotheses only need to be supplied for the single test function under
consideration.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_truncatedError
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzero : Summable (system.weight f))
    (hprime : Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilTruncatedResidualSide system cutoff f +
            errorSide cutoff f)
    (herror :
      Tendsto (fun cutoff : Nat => errorSide cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f := by
  have hzero_limit :=
    tendsto_guinandWeilTruncatedZeroSide system exhaustion f hzero
  have hzero_as_residual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (𝓝 (guinandWeilZeroSide system f)) :=
    hzero_limit.congr'
      (Eventually.of_forall fun cutoff => hfinite cutoff)
  have hresidual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (𝓝 (guinandWeilResidualSide system f + 0)) :=
    (tendsto_guinandWeilTruncatedResidualSide system f hprime).add herror
  have hlimit :
      guinandWeilZeroSide system f = guinandWeilResidualSide system f + 0 :=
    tendsto_nhds_unique hzero_as_residual_error hresidual_error
  simpa using hlimit

/--
Pointwise concrete source theorem when the residual cutoff is eventually
exactly the limiting residual side.  This is the compact-support-friendly route:
the limiting argument no longer needs prime-side summability or convergence.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_truncatedError_of_residualEventuallyEq
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzero : Summable (system.weight f))
    (hresidual :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedResidualSide system cutoff f =
          guinandWeilResidualSide system f)
    (hfinite :
      forall cutoff : Nat,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilTruncatedResidualSide system cutoff f +
            errorSide cutoff f)
    (herror :
      Tendsto (fun cutoff : Nat => errorSide cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f := by
  have hzero_limit :=
    tendsto_guinandWeilTruncatedZeroSide system exhaustion f hzero
  have hzero_as_residual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (𝓝 (guinandWeilZeroSide system f)) :=
    hzero_limit.congr'
      (Eventually.of_forall fun cutoff => hfinite cutoff)
  have hresidual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (𝓝 (guinandWeilResidualSide system f + 0)) :=
    (tendsto_guinandWeilTruncatedResidualSide_of_eventually_eq system f
      hresidual).add herror
  have hlimit :
      guinandWeilZeroSide system f = guinandWeilResidualSide system f + 0 :=
    tendsto_nhds_unique hzero_as_residual_error hresidual_error
  simpa using hlimit

/--
Pointwise concrete source theorem when both cutoff sides eventually stabilize
exactly.  This is the finite-support route: no zero summability or prime
summability hypothesis is needed once the two cutoff sides are eventually
constant at their limiting values.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_truncatedError_of_sidesEventuallyEq
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzeroSide :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilZeroSide system f)
    (hresidual :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedResidualSide system cutoff f =
          guinandWeilResidualSide system f)
    (hfinite :
      forall cutoff : Nat,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilTruncatedResidualSide system cutoff f +
            errorSide cutoff f)
    (herror :
      Tendsto (fun cutoff : Nat => errorSide cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f := by
  have hzero_limit :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f)
        atTop (𝓝 (guinandWeilZeroSide system f)) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : Nat => guinandWeilZeroSide system f)
        atTop (𝓝 (guinandWeilZeroSide system f))).congr'
          (hzeroSide.mono fun _ h => h.symm)
  have hzero_as_residual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (𝓝 (guinandWeilZeroSide system f)) :=
    hzero_limit.congr'
      (Eventually.of_forall fun cutoff => hfinite cutoff)
  have hresidual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f)
        atTop (𝓝 (guinandWeilResidualSide system f + 0)) :=
    (tendsto_guinandWeilTruncatedResidualSide_of_eventually_eq system f
      hresidual).add herror
  have hlimit :
      guinandWeilZeroSide system f = guinandWeilResidualSide system f + 0 :=
    tendsto_nhds_unique hzero_as_residual_error hresidual_error
  simpa using hlimit

/--
Compact support on both analytic sides gives the pointwise source formula from
the finite signed-error contour identity and signed-error convergence.  The
zero-side compact support supplies exact zero-cutoff stabilization, and compact
Fourier support supplies exact residual-cutoff stabilization, so no separate
zero-side or prime-side summability hypothesis is needed.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_truncatedError_of_compactSupports
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzeroSupport : ZetaZeroWeightSupportedInCompact K (system.weight f))
    (hfourier : GuinandWeilFourierCompactSupport f)
    (hfinite :
      forall cutoff : Nat,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilTruncatedResidualSide system cutoff f +
            errorSide cutoff f)
    (herror :
      Tendsto (fun cutoff : Nat => errorSide cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_truncatedError_of_sidesEventuallyEq
    system exhaustion errorSide f
    (eventually_guinandWeilTruncatedZeroSide_eq_zeroSide_of_supportedInCompact
      system exhaustion K hK f hzeroSupport)
    (eventually_guinandWeilTruncatedResidualSide_eq_residualSide_of_fourierCompactSupport
      system f hfourier)
    hfinite herror

/--
Pointwise concrete source theorem from an eventual absolute error envelope.
This is the shape used for a restricted analytic source class.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_truncatedEventualErrorEnvelope
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzero : Summable (system.weight f))
    (hprime : Summable (fun n : Nat => guinandWeilPrimeTerm f n))
    (hfinite :
      forall cutoff : Nat,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilTruncatedResidualSide system cutoff f +
            errorSide cutoff f)
    (herror_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |errorSide cutoff f| <= errorEnvelope cutoff f)
    (henvelope_zero :
      Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_truncatedError
    system exhaustion errorSide f hzero hprime hfinite
    (by
      have habs :
          Tendsto (fun cutoff : Nat => |errorSide cutoff f|)
            atTop (𝓝 0) :=
        squeeze_zero'
          (Eventually.of_forall
            (fun cutoff : Nat => abs_nonneg (errorSide cutoff f)))
          herror_bound
          henvelope_zero
      exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs)

/--
Eventual-envelope pointwise source theorem with exact eventual residual
stabilization.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_truncatedEventualErrorEnvelope_of_residualEventuallyEq
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzero : Summable (system.weight f))
    (hresidual :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedResidualSide system cutoff f =
          guinandWeilResidualSide system f)
    (hfinite :
      forall cutoff : Nat,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilTruncatedResidualSide system cutoff f +
            errorSide cutoff f)
    (herror_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |errorSide cutoff f| <= errorEnvelope cutoff f)
    (henvelope_zero :
      Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_truncatedError_of_residualEventuallyEq
    system exhaustion errorSide f hzero hresidual hfinite
    (by
      have habs :
          Tendsto (fun cutoff : Nat => |errorSide cutoff f|)
            atTop (𝓝 0) :=
        squeeze_zero'
          (Eventually.of_forall
            (fun cutoff : Nat => abs_nonneg (errorSide cutoff f)))
          herror_bound
          henvelope_zero
      exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs)

/--
Eventual-envelope source theorem when both cutoff sides are eventually exactly
their limiting sides.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_truncatedEventualErrorEnvelope_of_sidesEventuallyEq
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzeroSide :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilZeroSide system f)
    (hresidual :
      ∀ᶠ cutoff : Nat in atTop,
        guinandWeilTruncatedResidualSide system cutoff f =
          guinandWeilResidualSide system f)
    (hfinite :
      forall cutoff : Nat,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilTruncatedResidualSide system cutoff f +
            errorSide cutoff f)
    (herror_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |errorSide cutoff f| <= errorEnvelope cutoff f)
    (henvelope_zero :
      Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_truncatedError_of_sidesEventuallyEq
    system exhaustion errorSide f hzeroSide hresidual hfinite
    (by
      have habs :
          Tendsto (fun cutoff : Nat => |errorSide cutoff f|)
            atTop (𝓝 0) :=
        squeeze_zero'
          (Eventually.of_forall
            (fun cutoff : Nat => abs_nonneg (errorSide cutoff f)))
          herror_bound
          henvelope_zero
      exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs)

/--
For a compact-Fourier-support source test, the eventual-envelope contour
identity no longer needs a separate prime-summability hypothesis: compact
support makes the concrete prime side finite.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_truncatedEventualErrorEnvelope_of_fourierCompactSupport
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzero : Summable (system.weight f))
    (hfourier : GuinandWeilFourierCompactSupport f)
    (hfinite :
      forall cutoff : Nat,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilTruncatedResidualSide system cutoff f +
            errorSide cutoff f)
    (herror_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |errorSide cutoff f| <= errorEnvelope cutoff f)
    (henvelope_zero :
      Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_truncatedEventualErrorEnvelope_of_residualEventuallyEq
    system exhaustion errorSide errorEnvelope f hzero
    (eventually_guinandWeilTruncatedResidualSide_eq_residualSide_of_fourierCompactSupport
      system f hfourier)
    hfinite herror_bound henvelope_zero

/--
Compact support on both analytic sides gives the pointwise source formula from
only the finite signed-error contour identity and the decaying error envelope.
The zero-side compact support supplies exact zero-cutoff stabilization, and
compact Fourier support supplies exact residual-cutoff stabilization.
-/
theorem guinandWeilConcrete_sourceFormulaAt_of_truncatedEventualErrorEnvelope_of_compactSupports
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (errorSide errorEnvelope : Nat -> SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (hzeroSupport : ZetaZeroWeightSupportedInCompact K (system.weight f))
    (hfourier : GuinandWeilFourierCompactSupport f)
    (hfinite :
      forall cutoff : Nat,
        guinandWeilTruncatedZeroSide system
            (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
          guinandWeilTruncatedResidualSide system cutoff f +
            errorSide cutoff f)
    (herror_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |errorSide cutoff f| <= errorEnvelope cutoff f)
    (henvelope_zero :
      Tendsto (fun cutoff : Nat => errorEnvelope cutoff f) atTop (𝓝 0)) :
    guinandWeilZeroSide system f = guinandWeilResidualSide system f :=
  guinandWeilConcrete_sourceFormulaAt_of_truncatedEventualErrorEnvelope_of_sidesEventuallyEq
    system exhaustion errorSide errorEnvelope f
    (eventually_guinandWeilTruncatedZeroSide_eq_zeroSide_of_supportedInCompact
      system exhaustion K hK f hzeroSupport)
    (eventually_guinandWeilTruncatedResidualSide_eq_residualSide_of_fourierCompactSupport
      system f hfourier)
    hfinite herror_bound henvelope_zero

end

end RiemannHypothesisProject
