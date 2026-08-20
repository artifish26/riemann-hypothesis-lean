import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceKInjectivity
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# M100-DF6F inverse-Neumann source-energy completion

This module constructs the Hilbert completion induced by Suzuki's positive
inverse-Neumann form on the zero-mean interval source space.  The construction
is deliberately one-way: interval `L2` vectors form the dense algebraic core
of the energy completion.  No reverse embedding of the completion into
interval `L2` is asserted.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped InnerProductSpace ComplexConjugate

local instance suzukiSourceEnergyCompletionL2CompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- A type copy of the zero-mean interval source space, equipped below with
the inverse-Neumann energy norm rather than its ambient `L2` norm. -/
structure SuzukiSourceEnergyCore (a : Real) (ha : 0 < a) where
  toL2 : SuzukiFiniteIntervalZeroMeanL2 a

private def suzukiSourceEnergyCoreEquiv
    (a : Real) (ha : 0 < a) :
    SuzukiSourceEnergyCore a ha ≃ SuzukiFiniteIntervalZeroMeanL2 a where
  toFun := SuzukiSourceEnergyCore.toL2
  invFun := SuzukiSourceEnergyCore.mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (a : Real) (ha : 0 < a) :
    AddCommGroup (SuzukiSourceEnergyCore a ha) :=
  (suzukiSourceEnergyCoreEquiv a ha).addCommGroup

noncomputable instance (a : Real) (ha : 0 < a) :
    Module Complex (SuzukiSourceEnergyCore a ha) :=
  (suzukiSourceEnergyCoreEquiv a ha).module Complex

@[ext]
theorem SuzukiSourceEnergyCore.ext
    {a : Real} {ha : 0 < a} {u v : SuzukiSourceEnergyCore a ha}
    (h : u.toL2 = v.toL2) : u = v := by
  exact (suzukiSourceEnergyCoreEquiv a ha).injective h

@[simp]
theorem SuzukiSourceEnergyCore.toL2_zero
    {a : Real} {ha : 0 < a} :
    (0 : SuzukiSourceEnergyCore a ha).toL2 = 0 :=
  rfl

@[simp]
theorem SuzukiSourceEnergyCore.toL2_add
    {a : Real} {ha : 0 < a} (u v : SuzukiSourceEnergyCore a ha) :
    (u + v).toL2 = u.toL2 + v.toL2 :=
  rfl

@[simp]
theorem SuzukiSourceEnergyCore.toL2_smul
    {a : Real} {ha : 0 < a} (c : Complex)
    (u : SuzukiSourceEnergyCore a ha) :
    (c • u).toL2 = c • u.toL2 :=
  rfl

/-- The positive-definite inner-product core induced by `K_a`. -/
@[reducible] private def suzukiSourceEnergyInnerCore
    (a : Real) (ha : 0 < a) :
    InnerProductSpace.Core Complex (SuzukiSourceEnergyCore a ha) where
  inner u v := inner Complex (suzukiSourceKOperator a u.toL2) v.toL2
  conj_inner_symm u v := by
    calc
      conj (inner Complex (suzukiSourceKOperator a v.toL2) u.toL2) =
          inner Complex u.toL2 (suzukiSourceKOperator a v.toL2) :=
        inner_conj_symm u.toL2 (suzukiSourceKOperator a v.toL2)
      _ = inner Complex (suzukiSourceKOperator a u.toL2) v.toL2 :=
        (suzukiSourceKOperator_isSelfAdjoint a).isSymmetric u.toL2 v.toL2
          |>.symm
  re_inner_nonneg u := re_inner_suzukiSourceKOperator_nonneg ha u.toL2
  add_left u v w := by
    simp only [SuzukiSourceEnergyCore.toL2_add, map_add, inner_add_left]
  smul_left u v c := by
    simp only [SuzukiSourceEnergyCore.toL2_smul, map_smul]
    exact inner_smul_left (suzukiSourceKOperator a u.toL2) v.toL2 c
  definite u hinner := by
    apply SuzukiSourceEnergyCore.ext
    apply suzukiSourceKSeminorm_definite ha u.toL2
    unfold suzukiSourceKSeminorm
    change Real.sqrt
      (inner Complex (suzukiSourceKOperator a u.toL2) u.toL2).re = 0
    rw [hinner, Complex.zero_re, Real.sqrt_zero]

noncomputable instance (a : Real) (ha : 0 < a) :
    NormedAddCommGroup (SuzukiSourceEnergyCore a ha) := by
  exact @InnerProductSpace.Core.toNormedAddCommGroup
    Complex (SuzukiSourceEnergyCore a ha) _ _ _
      (suzukiSourceEnergyInnerCore a ha)

noncomputable instance (a : Real) (ha : 0 < a) :
    NormedSpace Complex (SuzukiSourceEnergyCore a ha) := by
  exact NormedSpace.ofCore
    (InnerProductSpace.Core.toNormedSpaceCore
      (suzukiSourceEnergyInnerCore a ha))

noncomputable instance (a : Real) (ha : 0 < a) :
    InnerProductSpace Complex (SuzukiSourceEnergyCore a ha) where
  __ := suzukiSourceEnergyInnerCore a ha
  norm_sq_eq_re_inner u := by
    change Real.sqrt
      (inner Complex (suzukiSourceKOperator a u.toL2) u.toL2).re ^ 2 = _
    exact Real.sq_sqrt (re_inner_suzukiSourceKOperator_nonneg ha u.toL2)

/-- The induced norm is exactly the inverse-Neumann source norm. -/
theorem norm_suzukiSourceEnergyCore
    {a : Real} {ha : 0 < a} (u : SuzukiSourceEnergyCore a ha) :
    ‖u‖ = suzukiSourceKSeminorm a u.toL2 := by
  rfl

/-- Suzuki's inverse-Neumann source-energy Hilbert completion. -/
abbrev SuzukiSourceEnergyCompletion (a : Real) (ha : 0 < a) :=
  UniformSpace.Completion (SuzukiSourceEnergyCore a ha)

/-- The canonical dense inclusion of the energy core into its completion. -/
def suzukiSourceEnergyCoreToCompletion
    (a : Real) (ha : 0 < a) :
    SuzukiSourceEnergyCore a ha →ₗᵢ[Complex]
      SuzukiSourceEnergyCompletion a ha :=
  UniformSpace.Completion.toComplₗᵢ

theorem denseRange_suzukiSourceEnergyCoreToCompletion
    (a : Real) (ha : 0 < a) :
    DenseRange (suzukiSourceEnergyCoreToCompletion a ha) := by
  simpa [suzukiSourceEnergyCoreToCompletion] using
    (UniformSpace.Completion.denseRange_coe :
      DenseRange (fun u : SuzukiSourceEnergyCore a ha =>
        (u : SuzukiSourceEnergyCompletion a ha)))

/-- A completion vector is interval-`L2` realizable exactly when it lies in
the canonical energy-core image.  This is a property of an individual vector,
not a reverse embedding of the entire completion. -/
def SuzukiSourceEnergyL2Realizable
    {a : Real} {ha : 0 < a}
    (x : SuzukiSourceEnergyCompletion a ha) : Prop :=
  x ∈ LinearMap.range (suzukiSourceEnergyCoreToCompletion a ha).toLinearMap

theorem suzukiSourceEnergyL2Realizable_iff
    {a : Real} {ha : 0 < a}
    {x : SuzukiSourceEnergyCompletion a ha} :
    SuzukiSourceEnergyL2Realizable x ↔
      ∃ u : SuzukiSourceEnergyCore a ha,
        suzukiSourceEnergyCoreToCompletion a ha u = x := by
  rfl

theorem suzukiSourceEnergyL2Realizable_core
    {a : Real} {ha : 0 < a} (u : SuzukiSourceEnergyCore a ha) :
    SuzukiSourceEnergyL2Realizable
      (suzukiSourceEnergyCoreToCompletion a ha u) := by
  exact ⟨u, rfl⟩

/-- Any realizable completion vector has a unique energy-core, hence a unique
zero-mean interval-`L2`, representative. -/
theorem existsUnique_suzukiSourceEnergyCore_of_L2Realizable
    {a : Real} {ha : 0 < a}
    {x : SuzukiSourceEnergyCompletion a ha}
    (hx : SuzukiSourceEnergyL2Realizable x) :
    ∃! u : SuzukiSourceEnergyCore a ha,
      suzukiSourceEnergyCoreToCompletion a ha u = x := by
  rcases hx with ⟨u, hu⟩
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact (suzukiSourceEnergyCoreToCompletion a ha).injective
    (hv.trans hu.symm)

/-- The uniquely extracted interval-`L2` representative of one realizable
completion vector. -/
noncomputable def suzukiSourceEnergyRealizedL2
    {a : Real} {ha : 0 < a}
    (x : SuzukiSourceEnergyCompletion a ha)
    (hx : SuzukiSourceEnergyL2Realizable x) :
    SuzukiFiniteIntervalZeroMeanL2 a :=
  (existsUnique_suzukiSourceEnergyCore_of_L2Realizable hx).choose.toL2

theorem suzukiSourceEnergyCoreToCompletion_realizedL2
    {a : Real} {ha : 0 < a}
    (x : SuzukiSourceEnergyCompletion a ha)
    (hx : SuzukiSourceEnergyL2Realizable x) :
    suzukiSourceEnergyCoreToCompletion a ha
        ⟨suzukiSourceEnergyRealizedL2 x hx⟩ = x := by
  exact (existsUnique_suzukiSourceEnergyCore_of_L2Realizable hx).choose_spec.1

theorem suzukiSourceEnergyRealizedL2_eq
    {a : Real} {ha : 0 < a}
    (x : SuzukiSourceEnergyCompletion a ha)
    (hx : SuzukiSourceEnergyL2Realizable x)
    (u : SuzukiSourceEnergyCore a ha)
    (hu : suzukiSourceEnergyCoreToCompletion a ha u = x) :
    suzukiSourceEnergyRealizedL2 x hx = u.toL2 := by
  have hchosen :=
    (existsUnique_suzukiSourceEnergyCore_of_L2Realizable hx).choose_spec.1
  have hcore :=
    (existsUnique_suzukiSourceEnergyCore_of_L2Realizable hx).unique
      hchosen hu
  change
    (existsUnique_suzukiSourceEnergyCore_of_L2Realizable hx).choose.toL2 =
      u.toL2
  exact congrArg SuzukiSourceEnergyCore.toL2 hcore

@[simp]
theorem norm_suzukiSourceEnergyCoreToCompletion
    {a : Real} {ha : 0 < a} (u : SuzukiSourceEnergyCore a ha) :
    ‖suzukiSourceEnergyCoreToCompletion a ha u‖ =
      suzukiSourceKSeminorm a u.toL2 := by
  rw [show ‖suzukiSourceEnergyCoreToCompletion a ha u‖ = ‖u‖ by
    simpa [suzukiSourceEnergyCoreToCompletion] using
      (UniformSpace.Completion.norm_coe u)]
  exact norm_suzukiSourceEnergyCore u

end

end RiemannHypothesisProject.Experiments.M100
