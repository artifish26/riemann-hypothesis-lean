import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaPrimitiveCoreDensity
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceFormPolarization
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# M100-DF6F unbounded source differential

This module constructs Suzuki's differential as a densely defined
`LinearPMap` from finite-interval `L2` to the zero-mean source space.  Its
domain is exactly the injective image of the compactly supported smooth
primitive core.  The Mathlib adjoint therefore has its genuine maximal
adjoint domain; no bounded surrogate for `D*` is introduced.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

local instance suzukiUnboundedDifferentialCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalL2 a) := by infer_instance

/-- The smooth primitive core identified with its injective image in interval
`L2`. -/
def suzukiSmoothPrimitiveCoreRangeEquiv (a : Real) :
    SuzukiSmoothCoreLinearSubmodule a ≃ₗ[Complex]
      LinearMap.range (suzukiSmoothCoreFiniteIntervalL2LinearMap a) :=
  LinearEquiv.ofInjective (suzukiSmoothCoreFiniteIntervalL2LinearMap a)
    (injective_suzukiSmoothCoreFiniteIntervalL2LinearMap a)

/-- Suzuki's `D=i d/dx` as a densely defined operator from primitive interval
`L2` to zero-mean source interval `L2`. -/
def suzukiSourceDifferentialPMap
    (a : Real) (ha : 0 < a) :
    SuzukiFiniteIntervalL2 a →ₗ.[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a where
  domain := LinearMap.range (suzukiSmoothCoreFiniteIntervalL2LinearMap a)
  toFun := (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha).comp
    (suzukiSmoothPrimitiveCoreRangeEquiv a).symm.toLinearMap

@[simp]
theorem suzukiSourceDifferentialPMap_domain
    (a : Real) (ha : 0 < a) :
    (suzukiSourceDifferentialPMap a ha).domain =
      LinearMap.range (suzukiSmoothCoreFiniteIntervalL2LinearMap a) :=
  rfl

/-- The unbounded differential agrees exactly with the previously checked
smooth differential receiving map. -/
@[simp]
theorem suzukiSourceDifferentialPMap_core_apply
    {a : Real} (ha : 0 < a)
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiSourceDifferentialPMap a ha
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap a v,
          LinearMap.mem_range_self
            (suzukiSmoothCoreFiniteIntervalL2LinearMap a) v⟩ =
      suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v := by
  change suzukiSmoothCoreDifferentialZeroMeanLinearMap ha
      ((suzukiSmoothPrimitiveCoreRangeEquiv a).symm
        ((suzukiSmoothPrimitiveCoreRangeEquiv a) v)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The unbounded differential has dense domain in primitive interval `L2`.
-/
theorem dense_suzukiSourceDifferentialPMap_domain
    {a : Real} (ha : 0 < a) :
    Dense ((suzukiSourceDifferentialPMap a ha).domain :
      Set (SuzukiFiniteIntervalL2 a)) := by
  change Dense
    (LinearMap.range (suzukiSmoothCoreFiniteIntervalL2LinearMap a) :
      Set (SuzukiFiniteIntervalL2 a))
  exact denseRange_suzukiSmoothCoreFiniteIntervalL2LinearMap ha

/-- The bounded screw operator composed after the densely defined
differential. -/
def suzukiSourceGDifferentialPMap
    (a : Real) (ha : 0 < a) :
    SuzukiFiniteIntervalL2 a →ₗ.[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a :=
  (suzukiSourceGOperator a).toLinearMap.compPMap
    (suzukiSourceDifferentialPMap a ha)

@[simp]
theorem suzukiSourceGDifferentialPMap_domain
    (a : Real) (ha : 0 < a) :
    (suzukiSourceGDifferentialPMap a ha).domain =
      (suzukiSourceDifferentialPMap a ha).domain :=
  rfl

@[simp]
theorem suzukiSourceGDifferentialPMap_core_apply
    {a : Real} (ha : 0 < a)
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiSourceGDifferentialPMap a ha
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap a v,
          LinearMap.mem_range_self
            (suzukiSmoothCoreFiniteIntervalL2LinearMap a) v⟩ =
      suzukiSourceGOperator a
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v) := by
  change suzukiSourceGOperator a
      (suzukiSourceDifferentialPMap a ha
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap a v,
          LinearMap.mem_range_self
            (suzukiSmoothCoreFiniteIntervalL2LinearMap a) v⟩) = _
  rw [suzukiSourceDifferentialPMap_core_apply]

/-- The exact remaining smooth-domain condition for the formal operator
`B_a=D*G_aD`: every `G_a Dv` must lie in the maximal adjoint domain of the
densely defined differential.  This is a source/operator-domain theorem, not
an endpoint record. -/
def SuzukiSourceGDifferentialInAdjointDomainAt
    (a : Real) (ha : 0 < a) : Prop :=
  ∀ x : (suzukiSourceGDifferentialPMap a ha).domain,
    suzukiSourceGDifferentialPMap a ha x ∈
      (suzukiSourceDifferentialPMap a ha)†.domain

/-- The adjoint-domain target is equivalently the explicit condition on every
smooth primitive. -/
theorem suzukiSourceGDifferentialInAdjointDomainAt_iff_core
    {a : Real} (ha : 0 < a) :
    SuzukiSourceGDifferentialInAdjointDomainAt a ha ↔
      ∀ v : SuzukiSmoothCoreLinearSubmodule a,
        suzukiSourceGOperator a
            (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v) ∈
          (suzukiSourceDifferentialPMap a ha)†.domain := by
  constructor
  · intro h v
    rw [← suzukiSourceGDifferentialPMap_core_apply ha v]
    exact h
      ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap a v,
        LinearMap.mem_range_self
          (suzukiSmoothCoreFiniteIntervalL2LinearMap a) v⟩
  · intro h x
    rcases x.2 with ⟨v, hv⟩
    have hx : x =
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap a v,
          LinearMap.mem_range_self
            (suzukiSmoothCoreFiniteIntervalL2LinearMap a) v⟩ :=
      Subtype.ext hv.symm
    rw [hx, suzukiSourceGDifferentialPMap_core_apply]
    exact h v

/-- Once the exact adjoint-domain theorem is supplied, the formal
`B_a=D*G_aD` operator exists on the whole smooth primitive domain. -/
def suzukiSourceBOperator
    {a : Real} (ha : 0 < a)
    (hdomain : SuzukiSourceGDifferentialInAdjointDomainAt a ha) :
    SuzukiFiniteIntervalL2 a →ₗ.[Complex]
      SuzukiFiniteIntervalL2 a :=
  (suzukiSourceDifferentialPMap a ha)†.comp
    (suzukiSourceGDifferentialPMap a ha) hdomain

/-- The formal adjoint identity gives the exact `D*G_aD` pairing on its smooth
domain. -/
theorem inner_suzukiSourceBOperator
    {a : Real} (ha : 0 < a)
    (hdomain : SuzukiSourceGDifferentialInAdjointDomainAt a ha)
    (u : (suzukiSourceBOperator ha hdomain).domain)
    (v : (suzukiSourceDifferentialPMap a ha).domain) :
    inner Complex (suzukiSourceBOperator ha hdomain u) v =
      inner Complex
        (suzukiSourceGDifferentialPMap a ha
          ⟨u.1, u.2⟩)
        (suzukiSourceDifferentialPMap a ha v) := by
  exact (LinearPMap.adjoint_isFormalAdjoint
    (dense_suzukiSourceDifferentialPMap_domain ha))
      ⟨suzukiSourceGDifferentialPMap a ha ⟨u.1, u.2⟩,
        hdomain ⟨u.1, u.2⟩⟩ v

/-- At the frozen endpoint, the formal unbounded `D*G_aD` operator has the
checked corrected complete-form pairing on every pair of smooth primitives.
The only extra premise is the explicit maximal-adjoint-domain condition. -/
theorem inner_suzukiSourceBOperator_core_eq_correctedCompleteForm
    (hsource : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (hdomain : SuzukiSourceGDifferentialInAdjointDomainAt
      suzukiProjectAStar suzukiProjectAStar_pos)
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    inner Complex
        (suzukiSourceBOperator suzukiProjectAStar_pos hdomain
          ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap
              suzukiProjectAStar u,
            LinearMap.mem_range_self
              (suzukiSmoothCoreFiniteIntervalL2LinearMap
                suzukiProjectAStar) u⟩)
        (suzukiSmoothCoreFiniteIntervalL2LinearMap
          suzukiProjectAStar v) =
      suzukiYoshidaCorrectedCompleteForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) := by
  let uB : (suzukiSourceBOperator suzukiProjectAStar_pos hdomain).domain :=
    ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
      LinearMap.mem_range_self
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar) u⟩
  let vD : (suzukiSourceDifferentialPMap suzukiProjectAStar
      suzukiProjectAStar_pos).domain :=
    ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar v,
      LinearMap.mem_range_self
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar) v⟩
  change inner Complex
      (suzukiSourceBOperator suzukiProjectAStar_pos hdomain uB) vD = _
  rw [inner_suzukiSourceBOperator suzukiProjectAStar_pos hdomain uB vD]
  dsimp only [uB, vD]
  rw [suzukiSourceGDifferentialPMap_core_apply,
    suzukiSourceDifferentialPMap_core_apply]
  exact inner_suzukiSourceGOperator_differentials_eq_correctedCompleteForm
    hsource u v

end

end RiemannHypothesisProject.Experiments.M100
