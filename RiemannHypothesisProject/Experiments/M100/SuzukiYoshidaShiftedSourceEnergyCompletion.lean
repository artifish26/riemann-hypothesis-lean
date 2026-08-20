import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceNormConsumer
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceKInjectivity
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# M100-DF6F shifted source-energy completion

Suzuki's deficiency vectors live in the Hilbert completion induced by the
shifted form `S_(a,lambda) = G_a - lambda K_a`, not merely in the completion
induced by `K_a`.  This module constructs that shifted completion on the
checked DF6E window.  The two independent source premises and the strict shift
bound remain explicit type indices.

As with the inverse-Neumann completion, the construction is deliberately
one-way: zero-mean interval `L2` vectors form the dense algebraic core.  No
embedding of the completed space back into interval `L2` is asserted.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped InnerProductSpace ComplexConjugate

local instance suzukiShiftedSourceEnergyCompletionL2CompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- A type copy of the zero-mean interval source space equipped below with the
shifted source-energy norm.  Its indices display exactly the checked source
premises and window restrictions needed for positive definiteness. -/
structure SuzukiShiftedSourceEnergyCore
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) where
  toL2 : SuzukiFiniteIntervalZeroMeanL2 a

private def suzukiShiftedSourceEnergyCoreEquiv
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda ≃
      SuzukiFiniteIntervalZeroMeanL2 a where
  toFun := SuzukiShiftedSourceEnergyCore.toL2
  invFun := SuzukiShiftedSourceEnergyCore.mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    AddCommGroup
      (SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda) :=
  (suzukiShiftedSourceEnergyCoreEquiv
    hsource hequation25 a ha lambda hlambda).addCommGroup

noncomputable instance
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    Module Complex
      (SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda) :=
  (suzukiShiftedSourceEnergyCoreEquiv
    hsource hequation25 a ha lambda hlambda).module Complex

@[ext]
theorem SuzukiShiftedSourceEnergyCore.ext
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    {u v : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda}
    (h : u.toL2 = v.toL2) : u = v := by
  exact (suzukiShiftedSourceEnergyCoreEquiv
    hsource hequation25 a ha lambda hlambda).injective h

@[simp]
theorem SuzukiShiftedSourceEnergyCore.toL2_zero
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)} :
    (0 : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda).toL2 = 0 :=
  rfl

@[simp]
theorem SuzukiShiftedSourceEnergyCore.toL2_add
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    (u v : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    (u + v).toL2 = u.toL2 + v.toL2 :=
  rfl

@[simp]
theorem SuzukiShiftedSourceEnergyCore.toL2_smul
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    (c : Complex)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    (c • u).toL2 = c • u.toL2 :=
  rfl

/-- The positive-definite inner-product core induced by `S_(a,lambda)` on the
checked DF6E window. -/
@[reducible] private def suzukiShiftedSourceEnergyInnerCore
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    InnerProductSpace.Core Complex
      (SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda) where
  inner u v :=
    inner Complex (suzukiSourceShiftedOperator a lambda u.toL2) v.toL2
  conj_inner_symm u v := by
    calc
      conj
          (inner Complex
            (suzukiSourceShiftedOperator a lambda v.toL2) u.toL2) =
          inner Complex u.toL2
            (suzukiSourceShiftedOperator a lambda v.toL2) :=
        inner_conj_symm u.toL2
          (suzukiSourceShiftedOperator a lambda v.toL2)
      _ = inner Complex
          (suzukiSourceShiftedOperator a lambda u.toL2) v.toL2 :=
        (suzukiSourceShiftedOperator_isSelfAdjoint a lambda).isSymmetric
          u.toL2 v.toL2 |>.symm
  re_inner_nonneg u :=
    re_inner_suzukiSourceShiftedOperator_nonneg
      hsource hequation25 ha hlambda u.toL2
  add_left u v w := by
    simp only [SuzukiShiftedSourceEnergyCore.toL2_add,
      map_add, inner_add_left]
  smul_left u v c := by
    simp only [SuzukiShiftedSourceEnergyCore.toL2_smul, map_smul]
    exact inner_smul_left
      (suzukiSourceShiftedOperator a lambda u.toL2) v.toL2 c
  definite u hinner := by
    apply SuzukiShiftedSourceEnergyCore.ext
    apply suzukiSourceKSeminorm_definite
      (suzukiDF6E_radius_pos ha) u.toL2
    unfold suzukiSourceKSeminorm
    have hk_nonneg := re_inner_suzukiSourceKOperator_nonneg
      (suzukiDF6E_radius_pos ha) u.toL2
    have hcoercive := suzukiDF6F_interval_shifted_source_coercive
      hsource hequation25 ha lambda u.toL2
    have hcoefficient : 0 < (1 / 400000 : Real) - lambda := by
      linarith
    have hshifted :
        (inner Complex
          (suzukiSourceShiftedOperator a lambda u.toL2) u.toL2).re = 0 := by
      rw [hinner]
      rfl
    have hk_zero :
        (inner Complex (suzukiSourceKOperator a u.toL2) u.toL2).re = 0 := by
      nlinarith
    rw [hk_zero, Real.sqrt_zero]

noncomputable instance
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    NormedAddCommGroup
      (SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda) := by
  exact @InnerProductSpace.Core.toNormedAddCommGroup
    Complex
    (SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) _ _ _
      (suzukiShiftedSourceEnergyInnerCore
        hsource hequation25 a ha lambda hlambda)

noncomputable instance
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    NormedSpace Complex
      (SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda) := by
  exact NormedSpace.ofCore
    (InnerProductSpace.Core.toNormedSpaceCore
      (suzukiShiftedSourceEnergyInnerCore
        hsource hequation25 a ha lambda hlambda))

noncomputable instance
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    InnerProductSpace Complex
      (SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda) where
  __ := suzukiShiftedSourceEnergyInnerCore
    hsource hequation25 a ha lambda hlambda
  norm_sq_eq_re_inner u := by
    change Real.sqrt
      (inner Complex
        (suzukiSourceShiftedOperator a lambda u.toL2) u.toL2).re ^ 2 = _
    exact Real.sq_sqrt
      (re_inner_suzukiSourceShiftedOperator_nonneg
        hsource hequation25 ha hlambda u.toL2)

/-- The shifted-energy core inner product is exactly the source-operator
pairing on the copied interval-`L2` vectors. -/
@[simp]
theorem inner_suzukiShiftedSourceEnergyCore
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    (u v : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    inner Complex u v =
      inner Complex
        (suzukiSourceShiftedOperator a lambda u.toL2) v.toL2 :=
  rfl

/-- The induced norm is exactly the shifted source-energy seminorm. -/
theorem norm_suzukiShiftedSourceEnergyCore
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    ‖u‖ = suzukiSourceShiftedSeminorm a lambda u.toL2 := by
  rfl

/-- Suzuki's shifted source-energy Hilbert completion `H(S_(a,lambda))` on
the checked DF6E window. -/
abbrev SuzukiShiftedSourceEnergyCompletion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :=
  UniformSpace.Completion
    (SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda)

/-- The canonical dense inclusion of the shifted-energy core into its
completion. -/
def suzukiShiftedSourceEnergyCoreToCompletion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda →ₗᵢ[Complex]
      SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda :=
  UniformSpace.Completion.toComplₗᵢ

theorem denseRange_suzukiShiftedSourceEnergyCoreToCompletion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    DenseRange
      (suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda) := by
  simpa [suzukiShiftedSourceEnergyCoreToCompletion] using
    (UniformSpace.Completion.denseRange_coe :
      DenseRange
        (fun u : SuzukiShiftedSourceEnergyCore
            hsource hequation25 a ha lambda hlambda =>
          (u : SuzukiShiftedSourceEnergyCompletion
            hsource hequation25 a ha lambda hlambda)))

/-- A shifted-completion vector is interval-`L2` realizable exactly when it
lies in the canonical shifted-energy-core image.  This is an individual-vector
property, not an embedding of the whole completion. -/
def SuzukiShiftedSourceEnergyL2Realizable
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda) : Prop :=
  x ∈ LinearMap.range
    (suzukiShiftedSourceEnergyCoreToCompletion
      hsource hequation25 a ha lambda hlambda).toLinearMap

theorem suzukiShiftedSourceEnergyL2Realizable_iff
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    {x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda} :
    SuzukiShiftedSourceEnergyL2Realizable x ↔
      ∃ u : SuzukiShiftedSourceEnergyCore
          hsource hequation25 a ha lambda hlambda,
        suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda u = x := by
  rfl

theorem suzukiShiftedSourceEnergyL2Realizable_core
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    SuzukiShiftedSourceEnergyL2Realizable
      (suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda u) := by
  exact ⟨u, rfl⟩

/-- Any realizable shifted-completion vector has a unique core and hence a
unique zero-mean interval-`L2` representative. -/
theorem existsUnique_suzukiShiftedSourceEnergyCore_of_L2Realizable
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    {x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda}
    (hx : SuzukiShiftedSourceEnergyL2Realizable x) :
    ∃! u : SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda,
      suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda u = x := by
  rcases hx with ⟨u, hu⟩
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact (suzukiShiftedSourceEnergyCoreToCompletion
    hsource hequation25 a ha lambda hlambda).injective
      (hv.trans hu.symm)

/-- The uniquely extracted interval-`L2` representative of one realizable
shifted-completion vector. -/
noncomputable def suzukiShiftedSourceEnergyRealizedL2
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (hx : SuzukiShiftedSourceEnergyL2Realizable x) :
    SuzukiFiniteIntervalZeroMeanL2 a :=
  (existsUnique_suzukiShiftedSourceEnergyCore_of_L2Realizable hx).choose.toL2

theorem suzukiShiftedSourceEnergyCoreToCompletion_realizedL2
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (hx : SuzukiShiftedSourceEnergyL2Realizable x) :
    suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda
        ⟨suzukiShiftedSourceEnergyRealizedL2 x hx⟩ = x := by
  exact
    (existsUnique_suzukiShiftedSourceEnergyCore_of_L2Realizable hx).choose_spec.1

@[simp]
theorem norm_suzukiShiftedSourceEnergyCoreToCompletion
    {hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar}
    {hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar}
    {a : Real} {ha : a ∈ SuzukiDF6EInterval}
    {lambda : Real} {hlambda : lambda < (1 / 400000 : Real)}
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    ‖suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda u‖ =
      suzukiSourceShiftedSeminorm a lambda u.toL2 := by
  rw [show
    ‖suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda u‖ = ‖u‖ by
      simpa [suzukiShiftedSourceEnergyCoreToCompletion] using
        (UniformSpace.Completion.norm_coe u)]
  exact norm_suzukiShiftedSourceEnergyCore u

end

end RiemannHypothesisProject.Experiments.M100
