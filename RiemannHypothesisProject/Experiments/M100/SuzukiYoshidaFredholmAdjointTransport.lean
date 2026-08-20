import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmAmbientTransport
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# M100-DF6F Fredholm adjoint-test transport

Suzuki's Section 8 calculation first identifies the ambient Fredholm equation
only through tests against the differential zero-mean core.  This module
formalizes the functional-analytic part of that passage: density promotes the
smooth tests to the full zero-mean space, the untested residual is exactly a
constant vector, and one scalar mean normalization recovers a literal ambient
equation.  It does not prove that Suzuki's source-domain calculation supplies
the tests or the normalization.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

local instance suzukiFredholmAdjointTransportCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- The ambient residual is orthogonal to the full zero-mean source space. -/
def SuzukiSourceAmbientAdjointIdentityAt
    (a lambda : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a)
    (rhs : SuzukiFiniteIntervalL2 a) : Prop :=
  ∀ v : SuzukiFiniteIntervalZeroMeanL2 a,
    inner Complex
      (suzukiSourceAmbientShiftedOperator a lambda u - rhs)
      (v : SuzukiFiniteIntervalL2 a) = 0

/-- The source-shaped version of the adjoint identity, tested only against
derivatives of compactly supported smooth primitives. -/
def SuzukiSourceAmbientSmoothAdjointIdentityAt
    {a : Real} (ha : 0 < a) (lambda : Real)
    (u : SuzukiFiniteIntervalZeroMeanL2 a)
    (rhs : SuzukiFiniteIntervalL2 a) : Prop :=
  ∀ v : SuzukiSmoothCore a,
    inner Complex
      (suzukiSourceAmbientShiftedOperator a lambda u - rhs)
      ((suzukiSmoothCoreDifferentialZeroMeanL2 ha v :
        SuzukiFiniteIntervalZeroMeanL2 a) : SuzukiFiniteIntervalL2 a) = 0

/-- The zero-mean source space is the orthogonal complement of the constant
line. -/
theorem suzukiFiniteIntervalZeroMeanSubspace_eq_span_one_orthogonal
    (a : Real) :
    SuzukiFiniteIntervalZeroMeanSubspace a =
      (Complex ∙ suzukiFiniteIntervalOneComplexL2 a)ᗮ := by
  ext v
  rw [mem_suzukiFiniteIntervalZeroMeanSubspace,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  rfl

/-- Consequently the directions invisible to all zero-mean tests are exactly
the constant line. -/
theorem suzukiFiniteIntervalZeroMeanSubspace_orthogonal_eq_span_one
    (a : Real) :
    (SuzukiFiniteIntervalZeroMeanSubspace a)ᗮ =
      Complex ∙ suzukiFiniteIntervalOneComplexL2 a := by
  rw [suzukiFiniteIntervalZeroMeanSubspace_eq_span_one_orthogonal]
  exact Submodule.orthogonal_orthogonal _

/-- The full adjoint identity is precisely orthogonality of the ambient
residual to the zero-mean source space. -/
theorem suzukiSourceAmbientAdjointIdentityAt_iff_mem_orthogonal
    {a lambda : Real} {u : SuzukiFiniteIntervalZeroMeanL2 a}
    {rhs : SuzukiFiniteIntervalL2 a} :
    SuzukiSourceAmbientAdjointIdentityAt a lambda u rhs ↔
      suzukiSourceAmbientShiftedOperator a lambda u - rhs ∈
        (SuzukiFiniteIntervalZeroMeanSubspace a)ᗮ := by
  rw [Submodule.mem_orthogonal']
  constructor
  · intro hadjoint v hv
    exact hadjoint ⟨v, hv⟩
  · intro horthogonal v
    exact horthogonal v v.2

/-- Constructive differential-core density promotes the source-shaped tests
to all zero-mean test vectors. -/
theorem suzukiSourceAmbientSmoothAdjointIdentityAt_iff_full
    {a : Real} (ha : 0 < a) {lambda : Real}
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    {rhs : SuzukiFiniteIntervalL2 a} :
    SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda u rhs ↔
      SuzukiSourceAmbientAdjointIdentityAt a lambda u rhs := by
  constructor
  . intro hsmooth v
    let p : SuzukiFiniteIntervalZeroMeanL2 a -> Prop := fun w =>
      inner Complex
        (suzukiSourceAmbientShiftedOperator a lambda u - rhs)
        (w : SuzukiFiniteIntervalL2 a) = 0
    apply DenseRange.induction_on (p := p)
      (suzukiSmoothDifferentialCoreDenseAt a ha) v
    . exact isClosed_eq (by fun_prop) (by fun_prop)
    . intro w
      exact hsmooth w
  . intro hfull v
    exact hfull (suzukiSmoothCoreDifferentialZeroMeanL2 ha v)

/-- The adjoint tests determine the ambient output up to one constant
deficiency coefficient, and no further ambiguity. -/
theorem suzukiSourceAmbientAdjointIdentityAt_iff_exists_const
    {a lambda : Real} {u : SuzukiFiniteIntervalZeroMeanL2 a}
    {rhs : SuzukiFiniteIntervalL2 a} :
    SuzukiSourceAmbientAdjointIdentityAt a lambda u rhs ↔
      ∃ c : Complex,
        suzukiSourceAmbientShiftedOperator a lambda u =
          rhs + c • suzukiFiniteIntervalOneComplexL2 a := by
  rw [suzukiSourceAmbientAdjointIdentityAt_iff_mem_orthogonal,
    suzukiFiniteIntervalZeroMeanSubspace_orthogonal_eq_span_one,
    Submodule.mem_span_singleton]
  constructor
  . rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hresidual :
        suzukiSourceAmbientShiftedOperator a lambda u - rhs =
          c • suzukiFiniteIntervalOneComplexL2 a := hc.symm
    exact (sub_eq_iff_eq_add.mp hresidual).trans (add_comm _ _)
  . rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc]
    abel

/-- A zero-mean residual that is also invisible to every zero-mean test must
vanish.  This is the abstract boundary-normalization step. -/
theorem suzukiSourceAmbientAdjointIdentityAt_eq_of_mean_eq
    {a lambda : Real} {u : SuzukiFiniteIntervalZeroMeanL2 a}
    {rhs : SuzukiFiniteIntervalL2 a}
    (hadjoint : SuzukiSourceAmbientAdjointIdentityAt a lambda u rhs)
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda u) =
      suzukiFiniteIntervalMeanCLM a rhs) :
    suzukiSourceAmbientShiftedOperator a lambda u = rhs := by
  let residual : SuzukiFiniteIntervalL2 a :=
    suzukiSourceAmbientShiftedOperator a lambda u - rhs
  have hzeroMean : residual ∈ SuzukiFiniteIntervalZeroMeanSubspace a := by
    rw [mem_suzukiFiniteIntervalZeroMeanSubspace]
    dsimp only [residual]
    rw [map_sub, hmean, sub_self]
  have horthogonal : residual ∈
      (SuzukiFiniteIntervalZeroMeanSubspace a)ᗮ :=
    suzukiSourceAmbientAdjointIdentityAt_iff_mem_orthogonal.mp hadjoint
  have hzero : residual = 0 := by
    have hmem : residual ∈
        (⊥ : Submodule Complex (SuzukiFiniteIntervalL2 a)) := by
      rw [← (SuzukiFiniteIntervalZeroMeanSubspace a).inf_orthogonal_eq_bot]
      exact ⟨hzeroMean, horthogonal⟩
    simpa using hmem
  exact sub_eq_zero.mp hzero

/-- A literal ambient equation is equivalent to the smooth source tests plus
the single scalar mean normalization that fixes the constant deficiency. -/
theorem suzukiSourceAmbientShiftedOperator_eq_iff_smoothAdjoint_and_mean
    {a : Real} (ha : 0 < a) {lambda : Real}
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    {rhs : SuzukiFiniteIntervalL2 a} :
    suzukiSourceAmbientShiftedOperator a lambda u = rhs ↔
      SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda u rhs ∧
        suzukiFiniteIntervalMeanCLM a
            (suzukiSourceAmbientShiftedOperator a lambda u) =
          suzukiFiniteIntervalMeanCLM a rhs := by
  constructor
  . intro heq
    constructor
    . intro v
      rw [heq, sub_self, inner_zero_left]
    . rw [heq]
  . rintro ⟨hadjoint, hmean⟩
    exact suzukiSourceAmbientAdjointIdentityAt_eq_of_mean_eq
      ((suzukiSourceAmbientSmoothAdjointIdentityAt_iff_full ha).mp hadjoint)
      hmean

/-- Plus-sign specialization for Suzuki's literal printed right-hand side. -/
theorem suzukiSourceAmbientShiftedOperator_eq_plus_iff_adjoint_and_mean
    {a : Real} (ha : 0 < a) {lambda : Real}
    {u : SuzukiFiniteIntervalZeroMeanL2 a} :
    suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmPlusContinuous a) ↔
      SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda u
          (suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmPlusContinuous a)) ∧
        suzukiFiniteIntervalMeanCLM a
            (suzukiSourceAmbientShiftedOperator a lambda u) =
          suzukiFiniteIntervalMeanCLM a
            (suzukiFiniteIntervalContinuousToL2 a
              (suzukiFredholmPlusContinuous a)) :=
  suzukiSourceAmbientShiftedOperator_eq_iff_smoothAdjoint_and_mean ha

/-- Minus-sign specialization for Suzuki's literal printed right-hand side. -/
theorem suzukiSourceAmbientShiftedOperator_eq_minus_iff_adjoint_and_mean
    {a : Real} (ha : 0 < a) {lambda : Real}
    {u : SuzukiFiniteIntervalZeroMeanL2 a} :
    suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmMinusContinuous a) ↔
      SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda u
          (suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmMinusContinuous a)) ∧
        suzukiFiniteIntervalMeanCLM a
            (suzukiSourceAmbientShiftedOperator a lambda u) =
          suzukiFiniteIntervalMeanCLM a
            (suzukiFiniteIntervalContinuousToL2 a
              (suzukiFredholmMinusContinuous a)) :=
  suzukiSourceAmbientShiftedOperator_eq_iff_smoothAdjoint_and_mean ha

/-- The plus source normalization is the explicit complex scalar selected by
the printed `exp x + i` right-hand side. -/
theorem suzukiSourceAmbientShiftedOperator_eq_plus_iff_adjoint_and_explicitMean
    {a : Real} (ha : 0 < a) {lambda : Real}
    {u : SuzukiFiniteIntervalZeroMeanL2 a} :
    suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmPlusContinuous a) ↔
      SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda u
          (suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmPlusContinuous a)) ∧
        suzukiFiniteIntervalMeanCLM a
            (suzukiSourceAmbientShiftedOperator a lambda u) =
          ((Real.exp a - Real.exp (-a) : Real) : Complex) +
            ((2 * a : Real) : Complex) * Complex.I := by
  rw [suzukiSourceAmbientShiftedOperator_eq_plus_iff_adjoint_and_mean ha,
    suzukiFiniteIntervalMeanCLM_fredholmPlus_eq ha]

/-- The minus source normalization is the conjugate-sign complex scalar
selected by the printed `exp (-x) - i` right-hand side. -/
theorem suzukiSourceAmbientShiftedOperator_eq_minus_iff_adjoint_and_explicitMean
    {a : Real} (ha : 0 < a) {lambda : Real}
    {u : SuzukiFiniteIntervalZeroMeanL2 a} :
    suzukiSourceAmbientShiftedOperator a lambda u =
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmMinusContinuous a) ↔
      SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda u
          (suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmMinusContinuous a)) ∧
        suzukiFiniteIntervalMeanCLM a
            (suzukiSourceAmbientShiftedOperator a lambda u) =
          ((Real.exp a - Real.exp (-a) : Real) : Complex) -
            ((2 * a : Real) : Complex) * Complex.I := by
  rw [suzukiSourceAmbientShiftedOperator_eq_minus_iff_adjoint_and_mean ha,
    suzukiFiniteIntervalMeanCLM_fredholmMinus_eq ha]

/-- Once the plus ambient adjoint and normalization inputs are supplied, the
checked projection bridge yields the projected equation consumed by the norm
estimate. -/
theorem suzukiSourceAmbientAdjoint_plus_implies_projected
    {a : Real} (ha : 0 < a) {lambda : Real}
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda u
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda u) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmPlusForcing a := by
  apply suzukiSourceAmbientShiftedOperator_solve_plus_implies_projected
  exact (suzukiSourceAmbientShiftedOperator_eq_plus_iff_adjoint_and_explicitMean ha).2
    ⟨hadjoint, hmean⟩

/-- The analogous adjoint-to-projected transport for the minus equation. -/
theorem suzukiSourceAmbientAdjoint_minus_implies_projected
    {a : Real} (ha : 0 < a) {lambda : Real}
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt ha lambda u
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda u) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmMinusForcing a := by
  apply suzukiSourceAmbientShiftedOperator_solve_minus_implies_projected
  exact (suzukiSourceAmbientShiftedOperator_eq_minus_iff_adjoint_and_explicitMean ha).2
    ⟨hadjoint, hmean⟩

/-- The live DF6F shifted plus estimate consumes the source adjoint tests and
mean normalization directly; the two independent endpoint source premises
remain explicit. -/
theorem suzukiDF6F_ambientAdjointPlus_sourceKSeminorm_le_five
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda u
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda u) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceKSeminorm a u ≤
      5 / ((1 / 400000 : Real) - lambda) := by
  apply suzukiDF6F_fredholmPlus_solution_sourceKSeminorm_le_five
    hsource hequation25 ha hlambda
  exact suzukiSourceAmbientAdjoint_plus_implies_projected
    (suzukiDF6E_radius_pos ha) hadjoint hmean

/-- The analogous direct DF6F consumer for the minus equation. -/
theorem suzukiDF6F_ambientAdjointMinus_sourceKSeminorm_le_five
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) lambda u
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a lambda u) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceKSeminorm a u ≤
      5 / ((1 / 400000 : Real) - lambda) := by
  apply suzukiDF6F_fredholmMinus_solution_sourceKSeminorm_le_five
    hsource hequation25 ha hlambda
  exact suzukiSourceAmbientAdjoint_minus_implies_projected
    (suzukiDF6E_radius_pos ha) hadjoint hmean

/-- At zero shift, the plus adjoint data give the frozen numerical bound
`2000000` without an extra projected-equation hypothesis. -/
theorem suzukiDF6F_ambientAdjointPlus_sourceKSeminorm_le_twoMillion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) 0 u
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a 0 u) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceKSeminorm a u ≤ 2000000 := by
  apply suzukiDF6F_sourceG_fredholmPlus_solution_sourceKSeminorm_le_twoMillion
    hsource hequation25 ha
  have hsolve := suzukiSourceAmbientAdjoint_plus_implies_projected
    (suzukiDF6E_radius_pos ha) hadjoint hmean
  simpa [suzukiSourceShiftedOperator] using hsolve

/-- Zero-shift numerical bound from the minus adjoint data. -/
theorem suzukiDF6F_ambientAdjointMinus_sourceKSeminorm_le_twoMillion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hadjoint : SuzukiSourceAmbientSmoothAdjointIdentityAt
      (suzukiDF6E_radius_pos ha) 0 u
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)))
    (hmean : suzukiFiniteIntervalMeanCLM a
        (suzukiSourceAmbientShiftedOperator a 0 u) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    suzukiSourceKSeminorm a u ≤ 2000000 := by
  apply suzukiDF6F_sourceG_fredholmMinus_solution_sourceKSeminorm_le_twoMillion
    hsource hequation25 ha
  have hsolve := suzukiSourceAmbientAdjoint_minus_implies_projected
    (suzukiDF6E_radius_pos ha) hadjoint hmean
  simpa [suzukiSourceShiftedOperator] using hsolve

end

end RiemannHypothesisProject.Experiments.M100
