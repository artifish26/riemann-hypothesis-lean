import RiemannHypothesisProject.Experiments.M100.SuzukiL2SupportGeometry

/-!
# M100-DF6D2 Suzuki source form-domain receiving bridge

This experimental module records the narrow Lean surface needed to receive
Suzuki's source form-domain theorems.  It embeds the existing smooth core into
the concrete global `L^2` quotient, uses a dedicated domain type so the form
topology cannot silently default to the ambient `L^2` topology, and exposes
every density and continuity input required by the DF6C closure theorem.

It also proves the elementary shifted-form comparison supplied by a bounded
`L^2` perturbation.  It does not prove the source form-core theorem, closability
of the singular form, equality of the local and complete form domains, or the
required form-topology continuities.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal

/-- The global `L^2` class represented by a Suzuki smooth-core function. -/
def suzukiSmoothCoreToL2 {r : Real} (v : SuzukiSmoothCore r) : SuzukiL2 :=
  (v.1.memLp (2 : ENNReal) (volume : Measure Real)).toLp v.1

/-- Pointwise support of the smooth representative descends through `toLp` to
the representative-independent almost-everywhere support predicate. -/
theorem suzukiSmoothCoreToL2_supportedAt {r : Real}
    (v : SuzukiSmoothCore r) :
    suzukiL2SupportedAt r (suzukiSmoothCoreToL2 v) := by
  apply suzukiL2SupportedAt_toLp_of_functionSupport
    (v.1.memLp (2 : ENNReal) (volume : Measure Real))
  intro x hx
  exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩

/-- The smooth-core map commutes with the unchanged-representative zero
extension before any closed form topology is introduced. -/
theorem suzukiSmoothCoreToL2_zeroExtension
    {a b : Real} (hab : a ≤ b) (v : SuzukiSmoothCore a) :
    suzukiSmoothCoreToL2 (suzukiSmoothCoreZeroExtension hab v) =
      suzukiSmoothCoreToL2 v := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    ((suzukiSmoothCoreZeroExtension hab v).1.memLp
      (2 : ENNReal) (volume : Measure Real)).coeFn_toLp,
    (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp]
      with x hxLarge hxSmall
  calc
    (suzukiSmoothCoreToL2
        (suzukiSmoothCoreZeroExtension hab v) : Real → Complex) x =
        (suzukiSmoothCoreZeroExtension hab v).1 x := by
      simpa only [suzukiSmoothCoreToL2] using hxLarge
    _ = v.1 x := rfl
    _ = (suzukiSmoothCoreToL2 v : Real → Complex) x := by
      symm
      simpa only [suzukiSmoothCoreToL2] using hxSmall

/-- A source form domain at radius `r`.  This is deliberately a fresh
structure rather than a subtype carrying the ambient topology: callers must
supply the actual shifted form topology before using density or continuity.
-/
@[ext]
structure SuzukiL2SourceFormDomain (globalDomain : Set SuzukiL2) (r : Real)
    where
  toL2 : SuzukiL2
  mem_globalDomain : toL2 ∈ globalDomain
  supportedAt : suzukiL2SupportedAt r toL2

/-- Zero extension on a source form domain leaves the global `L^2` class
unchanged and widens only its support certificate. -/
def suzukiL2SourceFormDomainZeroExtension
    {globalDomain : Set SuzukiL2} {a b : Real} (hab : a ≤ b) :
    SuzukiL2SourceFormDomain globalDomain a →
      SuzukiL2SourceFormDomain globalDomain b :=
  fun v ↦ ⟨v.toL2, v.mem_globalDomain,
    suzukiL2SupportedAt_mono hab v.supportedAt⟩

@[simp]
theorem suzukiL2SourceFormDomainZeroExtension_apply
    {globalDomain : Set SuzukiL2} {a b : Real} (hab : a ≤ b)
    (v : SuzukiL2SourceFormDomain globalDomain a) :
    (suzukiL2SourceFormDomainZeroExtension hab v).toL2 = v.toL2 :=
  rfl

theorem suzukiL2SourceFormDomainZeroExtension_injective
    {globalDomain : Set SuzukiL2} {a b : Real} (hab : a ≤ b) :
    Function.Injective
      (suzukiL2SourceFormDomainZeroExtension
        (globalDomain := globalDomain) hab) := by
  intro u v huv
  apply SuzukiL2SourceFormDomain.ext
  exact congrArg (fun w ↦ w.toL2) huv

@[simp]
theorem suzukiL2SourceFormDomainZeroExtension_norm
    {globalDomain : Set SuzukiL2} {a b : Real} (hab : a ≤ b)
    (v : SuzukiL2SourceFormDomain globalDomain a) :
    ‖(suzukiL2SourceFormDomainZeroExtension hab v).toL2‖ =
      ‖v.toL2‖ :=
  rfl

/-- Embed the smooth core into a named source domain once core membership is
supplied.  Membership is a separate source/normalization input. -/
def suzukiSmoothCoreToSourceFormDomain
    {globalDomain : Set SuzukiL2} {r : Real}
    (hcoreMem : ∀ v : SuzukiSmoothCore r,
      suzukiSmoothCoreToL2 v ∈ globalDomain) :
    SuzukiSmoothCore r → SuzukiL2SourceFormDomain globalDomain r :=
  fun v ↦ ⟨suzukiSmoothCoreToL2 v, hcoreMem v,
    suzukiSmoothCoreToL2_supportedAt v⟩

/-- Compatibility of the concrete smooth-core map and source-domain zero
extension. -/
theorem suzukiSmoothCoreToSourceFormDomain_zeroExtension
    {globalDomain : Set SuzukiL2} {a b : Real} (hab : a ≤ b)
    (hcoreMemSmall : ∀ v : SuzukiSmoothCore a,
      suzukiSmoothCoreToL2 v ∈ globalDomain)
    (hcoreMemLarge : ∀ v : SuzukiSmoothCore b,
      suzukiSmoothCoreToL2 v ∈ globalDomain)
    (v : SuzukiSmoothCore a) :
    suzukiL2SourceFormDomainZeroExtension hab
        (suzukiSmoothCoreToSourceFormDomain hcoreMemSmall v) =
      suzukiSmoothCoreToSourceFormDomain hcoreMemLarge
        (suzukiSmoothCoreZeroExtension hab v) := by
  apply SuzukiL2SourceFormDomain.ext
  exact (suzukiSmoothCoreToL2_zeroExtension hab v).symm

/-- A shifted diagonal form expression.  The shift must be chosen from an
actual lower bound; this definition alone does not supply a form norm. -/
def suzukiShiftedFormNormSq
    {E : Type*} [Norm E] (form : E → Real) (shift : Real) (v : E) : Real :=
  form v + shift * ‖v‖ ^ 2

/-- A bounded ambient-`L^2` perturbation gives explicit two-sided comparison
of positive shifted form-norm squares on the common core.

The local shift is `lower + 1`; the perturbed shift is
`lower + bound + 1`.  This is the elementary algebraic input for a later
completion/domain-equivalence proof, not that proof itself. -/
theorem suzukiShiftedFormNormSq_boundedPerturbation_comparison
    {E : Type*} [Norm E]
    (localForm boundedPart : E → Real) (lower bound : Real)
    (hboundNonneg : 0 ≤ bound)
    (hlower : ∀ v,
      -(lower * ‖v‖ ^ 2) ≤ localForm v)
    (hbounded : ∀ v,
      |boundedPart v| ≤ bound * ‖v‖ ^ 2)
    (v : E) :
    let localNormSq :=
      suzukiShiftedFormNormSq localForm (lower + 1) v
    let completeNormSq :=
      suzukiShiftedFormNormSq
        (fun w ↦ localForm w + boundedPart w)
        (lower + bound + 1) v
    0 ≤ localNormSq ∧
      localNormSq ≤ completeNormSq ∧
      completeNormSq ≤ (1 + 2 * bound) * localNormSq := by
  dsimp only [suzukiShiftedFormNormSq]
  have hnormSq : 0 ≤ ‖v‖ ^ 2 := sq_nonneg ‖v‖
  have hsemibounded : 0 ≤ localForm v + lower * ‖v‖ ^ 2 := by
    linarith [hlower v]
  have hlocalNonneg :
      0 ≤ localForm v + (lower + 1) * ‖v‖ ^ 2 := by
    nlinarith
  have hnorm_le_local :
      ‖v‖ ^ 2 ≤ localForm v + (lower + 1) * ‖v‖ ^ 2 := by
    nlinarith
  have hboundedLower :
      -(bound * ‖v‖ ^ 2) ≤ boundedPart v :=
    (abs_le.mp (hbounded v)).1
  have hboundedUpper :
      boundedPart v ≤ bound * ‖v‖ ^ 2 :=
    (abs_le.mp (hbounded v)).2
  have hlocal_le_complete :
      localForm v + (lower + 1) * ‖v‖ ^ 2 ≤
        localForm v + boundedPart v +
          (lower + bound + 1) * ‖v‖ ^ 2 := by
    nlinarith
  have hscale :
      2 * bound * ‖v‖ ^ 2 ≤
        2 * bound * (localForm v + (lower + 1) * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hnorm_le_local (by positivity)
  have hcomplete_le :
      localForm v + boundedPart v +
          (lower + bound + 1) * ‖v‖ ^ 2 ≤
        (1 + 2 * bound) *
          (localForm v + (lower + 1) * ‖v‖ ^ 2) := by
    nlinarith
  exact ⟨hlocalNonneg, hlocal_le_complete, hcomplete_le⟩

/-- Conditional DF6D2 receiving theorem.  Each hard source input is a separate
hypothesis, and the fresh domain structures carry only the form topologies
supplied by the caller.  In particular, ambient `L^2` density cannot satisfy
`hcoreDense` by typeclass inference.
-/
theorem suzukiL2SourceClosedLocalEnergyNesting_of_core
    {globalDomain : Set SuzukiL2} {a b : Real}
    [TopologicalSpace (SuzukiL2SourceFormDomain globalDomain a)]
    [TopologicalSpace (SuzukiL2SourceFormDomain globalDomain b)]
    (hab : a ≤ b)
    (hcoreMem : ∀ v : SuzukiSmoothCore a,
      suzukiSmoothCoreToL2 v ∈ globalDomain)
    (smallEnergy :
      SuzukiL2SourceFormDomain globalDomain a →
        SuzukiL2SourceFormDomain globalDomain a → Complex)
    (largeEnergy :
      SuzukiL2SourceFormDomain globalDomain b →
        SuzukiL2SourceFormDomain globalDomain b → Complex)
    (hcoreDense : DenseRange
      (suzukiSmoothCoreToSourceFormDomain hcoreMem))
    (hzeroContinuous : Continuous
      (suzukiL2SourceFormDomainZeroExtension
        (globalDomain := globalDomain) hab))
    (hsmallContinuous : Continuous (Function.uncurry smallEnergy))
    (hlargeContinuous : Continuous (Function.uncurry largeEnergy))
    (hcoreDifference : ∀ u v : SuzukiSmoothCore a,
      largeEnergy
          (suzukiL2SourceFormDomainZeroExtension hab
            (suzukiSmoothCoreToSourceFormDomain hcoreMem u))
          (suzukiL2SourceFormDomainZeroExtension hab
            (suzukiSmoothCoreToSourceFormDomain hcoreMem v)) -
        smallEnergy
          (suzukiSmoothCoreToSourceFormDomain hcoreMem u)
          (suzukiSmoothCoreToSourceFormDomain hcoreMem v) =
        suzukiCoreLocalEnergyRadiusIncrement a b
          (suzukiSmoothCorePolarizedWeight u v)) :
    ∀ u v,
      largeEnergy
          (suzukiL2SourceFormDomainZeroExtension hab u)
          (suzukiL2SourceFormDomainZeroExtension hab v) =
        smallEnergy u v := by
  exact suzukiClosedLocalEnergyNesting_of_core hab
    (suzukiSmoothCoreToSourceFormDomain hcoreMem)
    (suzukiL2SourceFormDomainZeroExtension hab)
    smallEnergy largeEnergy suzukiSmoothCorePolarizedWeight
    hcoreDense hzeroContinuous hsmallContinuous hlargeContinuous
    hcoreDifference

end

end M100
end Experiments
end RiemannHypothesisProject
