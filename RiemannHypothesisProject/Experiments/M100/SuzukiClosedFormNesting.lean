import RiemannHypothesisProject.Experiments.M100.SuzukiCoreLocalEnergyNesting
import Mathlib.Topology.DenseEmbedding

/-!
# M100-DF6C Suzuki closed-form nesting

This experimental module lifts the DF6B smooth-core radius cancellation to a
closed local-energy domain under explicit density and continuity hypotheses.
It also formalizes Suzuki's global-restriction convention: radius-dependent
domains are subtypes of one global form domain, and zero extension is literal
inclusion of the same global representative.

The hard source inputs remain visible.  In particular, callers must supply
core density in the form topology, continuity of the closed forms and zero
extension, equality of the local and complete global domains, and both
directions of the outer-annulus support characterization.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

/-- A radius restriction of one global closed form domain.  The predicate
`supportedAt r` may be instantiated by almost-everywhere support in `[-r,r]`.
-/
def SuzukiClosedRestrictionDomain
    {E : Type*} (globalDomain : Set E) (supportedAt : Real → E → Prop)
    (r : Real) : Type _ :=
  {v : E // v ∈ globalDomain ∧ supportedAt r v}

/-- Zero extension between two global-restriction realizations.  The ambient
representative is unchanged; only the support certificate is widened. -/
def suzukiClosedRestrictionZeroExtension
    {E : Type*} {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {a b : Real}
    (hsupportMono : ∀ ⦃v : E⦄, supportedAt a v → supportedAt b v) :
    SuzukiClosedRestrictionDomain globalDomain supportedAt a →
      SuzukiClosedRestrictionDomain globalDomain supportedAt b :=
  fun v => ⟨v.1, v.2.1, hsupportMono v.2.2⟩

@[simp]
theorem suzukiClosedRestrictionZeroExtension_apply
    {E : Type*} {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {a b : Real}
    (hsupportMono : ∀ ⦃v : E⦄, supportedAt a v → supportedAt b v)
    (v : SuzukiClosedRestrictionDomain globalDomain supportedAt a) :
    (suzukiClosedRestrictionZeroExtension hsupportMono v).1 = v.1 := rfl

/-- Zero extension is injective because the global representative is
unchanged. -/
theorem suzukiClosedRestrictionZeroExtension_injective
    {E : Type*} {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {a b : Real}
    (hsupportMono : ∀ ⦃v : E⦄, supportedAt a v → supportedAt b v) :
    Function.Injective
      (suzukiClosedRestrictionZeroExtension
        (globalDomain := globalDomain) hsupportMono) := by
  intro u v huv
  apply Subtype.ext
  exact congrArg (fun w => w.1) huv

/-- In the common-global-space convention, zero extension preserves the
ambient norm exactly. -/
@[simp]
theorem suzukiClosedRestrictionZeroExtension_norm
    {E : Type*} [Norm E]
    {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {a b : Real}
    (hsupportMono : ∀ ⦃v : E⦄, supportedAt a v → supportedAt b v)
    (v : SuzukiClosedRestrictionDomain globalDomain supportedAt a) :
    ‖(suzukiClosedRestrictionZeroExtension hsupportMono v).1‖ = ‖v.1‖ := rfl

/-- Every property of the unchanged global representative is preserved.  This
is the common mechanism for parity and zero-mean constraints. -/
theorem suzukiClosedRestrictionZeroExtension_preserves_globalProperty
    {E : Type*} {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {a b : Real}
    (hsupportMono : ∀ ⦃v : E⦄, supportedAt a v → supportedAt b v)
    (property : E → Prop)
    (v : SuzukiClosedRestrictionDomain globalDomain supportedAt a) :
    property (suzukiClosedRestrictionZeroExtension hsupportMono v).1 ↔
      property v.1 :=
  Iff.rfl

/-- Reflection-fixed constraints, hence even and odd eigenspace predicates
after choosing the corresponding symmetry, are unchanged by zero extension.
-/
theorem suzukiClosedRestrictionZeroExtension_preserves_fixedPoint
    {E : Type*} {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {a b : Real}
    (hsupportMono : ∀ ⦃v : E⦄, supportedAt a v → supportedAt b v)
    (symmetry : E → E)
    (v : SuzukiClosedRestrictionDomain globalDomain supportedAt a) :
    symmetry (suzukiClosedRestrictionZeroExtension hsupportMono v).1 =
        (suzukiClosedRestrictionZeroExtension hsupportMono v).1 ↔
      symmetry v.1 = v.1 :=
  Iff.rfl

/-- A global linear-functional constraint such as zero mean is unchanged by
zero extension.  Linearity is not needed for this identity. -/
theorem suzukiClosedRestrictionZeroExtension_preserves_zeroFunctional
    {E Value : Type*} [Zero Value]
    {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {a b : Real}
    (hsupportMono : ∀ ⦃v : E⦄, supportedAt a v → supportedAt b v)
    (functional : E → Value)
    (v : SuzukiClosedRestrictionDomain globalDomain supportedAt a) :
    functional (suzukiClosedRestrictionZeroExtension hsupportMono v).1 = 0 ↔
      functional v.1 = 0 :=
  Iff.rfl

/-- Exact image of zero extension.  The two support implications are kept as
separate hypotheses so the reverse closed-domain inclusion cannot be hidden.
-/
theorem suzukiClosedRestrictionZeroExtension_range
    {E : Type*} {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {a b : Real}
    (outerVanishing : E → Prop)
    (hsupportMono : ∀ ⦃v : E⦄, supportedAt a v → supportedAt b v)
    (houterOfSmall : ∀ ⦃v : E⦄,
      v ∈ globalDomain → supportedAt a v → outerVanishing v)
    (hsmallOfLargeOuter : ∀ ⦃v : E⦄,
      v ∈ globalDomain → supportedAt b v → outerVanishing v → supportedAt a v) :
    Set.range (suzukiClosedRestrictionZeroExtension hsupportMono) =
      {w : SuzukiClosedRestrictionDomain globalDomain supportedAt b |
        outerVanishing w.1} := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact houterOfSmall v.2.1 v.2.2
  · intro hw
    refine ⟨⟨w.1, w.2.1,
      hsmallOfLargeOuter w.2.1 w.2.2 hw⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Equality of the source local-energy and complete-form global domains gives
an exact equivalence of every radius restriction.  This is the explicit
bounded-perturbation domain input in the DF6C assembly. -/
def suzukiClosedRestrictionDomainEquivOfGlobalDomainEq
    {E : Type*} {localDomain completeDomain : Set E}
    {supportedAt : Real → E → Prop} {r : Real}
    (hdomains : localDomain = completeDomain) :
    SuzukiClosedRestrictionDomain localDomain supportedAt r ≃
      SuzukiClosedRestrictionDomain completeDomain supportedAt r := by
  subst completeDomain
  exact Equiv.refl _

/-- A complete form restricted from one global Hermitian form. -/
def suzukiRestrictedCompleteForm
    {E : Type*} {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {r : Real} (globalForm : E → E → Complex)
    (u v : SuzukiClosedRestrictionDomain globalDomain supportedAt r) : Complex :=
  globalForm u.1 v.1

/-- Complete-form nesting is exact because both radius restrictions evaluate
the same global representatives in the same global form. -/
@[simp]
theorem suzukiRestrictedCompleteForm_zeroExtension
    {E : Type*} {globalDomain : Set E} {supportedAt : Real → E → Prop}
    {a b : Real}
    (globalForm : E → E → Complex)
    (hsupportMono : ∀ ⦃v : E⦄, supportedAt a v → supportedAt b v)
    (u v : SuzukiClosedRestrictionDomain globalDomain supportedAt a) :
    suzukiRestrictedCompleteForm globalForm
        (suzukiClosedRestrictionZeroExtension hsupportMono u)
        (suzukiClosedRestrictionZeroExtension hsupportMono v) =
      suzukiRestrictedCompleteForm globalForm u v := rfl

/-- DF6C closure principle.  If the closed local forms and zero extension are
continuous in the closed form topologies, a dense-core difference equal to the
DF6B radius increment vanishes on the entire closed domain. -/
theorem suzukiClosedLocalEnergyNesting_of_core
    {Core DomainSmall DomainLarge : Type*}
    [TopologicalSpace DomainSmall] [TopologicalSpace DomainLarge]
    {a b : Real} (hab : a ≤ b)
    (coreInclusion : Core → DomainSmall)
    (zeroExtension : DomainSmall → DomainLarge)
    (smallEnergy : DomainSmall → DomainSmall → Complex)
    (largeEnergy : DomainLarge → DomainLarge → Complex)
    (weight : Core → Core → Real → Complex)
    (hcoreDense : DenseRange coreInclusion)
    (hzeroContinuous : Continuous zeroExtension)
    (hsmallContinuous : Continuous (Function.uncurry smallEnergy))
    (hlargeContinuous : Continuous (Function.uncurry largeEnergy))
    (hcoreDifference : ∀ u v,
      largeEnergy (zeroExtension (coreInclusion u))
          (zeroExtension (coreInclusion v)) -
        smallEnergy (coreInclusion u) (coreInclusion v) =
          suzukiCoreLocalEnergyRadiusIncrement a b (weight u v)) :
    ∀ u v,
      largeEnergy (zeroExtension u) (zeroExtension v) = smallEnergy u v := by
  intro u v
  refine hcoreDense.induction_on₂
    (p := fun x y =>
      largeEnergy (zeroExtension x) (zeroExtension y) = smallEnergy x y)
    ?_ ?_ u v
  · apply isClosed_eq
    · exact hlargeContinuous.comp
        ((hzeroContinuous.comp continuous_fst).prodMk
          (hzeroContinuous.comp continuous_snd))
    · exact hsmallContinuous
  · intro x y
    apply sub_eq_zero.mp
    calc
      largeEnergy (zeroExtension (coreInclusion x))
            (zeroExtension (coreInclusion y)) -
          smallEnergy (coreInclusion x) (coreInclusion y) =
          suzukiCoreLocalEnergyRadiusIncrement a b (weight x y) :=
        hcoreDifference x y
      _ = 0 := suzukiCoreLocalEnergyRadiusIncrement_eq_zero hab _

/-- Squared form norm associated to an explicit ambient norm-square and a
closed local energy.  Taking the real part keeps the definition honest for a
complex-polarized form. -/
def suzukiClosedFormNormSq
    {Domain : Type*} (normSq : Domain → Real)
    (energy : Domain → Domain → Complex) (v : Domain) : Real :=
  normSq v + (energy v v).re

/-- Closed local-energy nesting plus ambient norm preservation gives exact
form-norm preservation. -/
theorem suzukiClosedFormNormSq_zeroExtension
    {DomainSmall DomainLarge : Type*}
    (zeroExtension : DomainSmall → DomainLarge)
    (smallNormSq : DomainSmall → Real)
    (largeNormSq : DomainLarge → Real)
    (smallEnergy : DomainSmall → DomainSmall → Complex)
    (largeEnergy : DomainLarge → DomainLarge → Complex)
    (hnorm : ∀ v, largeNormSq (zeroExtension v) = smallNormSq v)
    (henergy : ∀ u v,
      largeEnergy (zeroExtension u) (zeroExtension v) = smallEnergy u v)
    (v : DomainSmall) :
    suzukiClosedFormNormSq largeNormSq largeEnergy (zeroExtension v) =
      suzukiClosedFormNormSq smallNormSq smallEnergy v := by
  rw [suzukiClosedFormNormSq, suzukiClosedFormNormSq, hnorm v, henergy v v]

end

end M100
end Experiments
end RiemannHypothesisProject
