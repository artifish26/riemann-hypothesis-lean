import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaDifferentialCoreDensity
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# M100-DF6F source-norm consumer

This module extracts the narrow norm consequence needed downstream from the
full-space DF6F source coercivity theorem.  The two endpoint source premises
remain visible.  No ambient inverse for the compact source operators is
asserted.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace ComplexConjugate

local instance suzukiSourceNormConsumerCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- The inverse-Neumann quadratic is nonnegative on the full zero-mean source
space.  Density of smooth differentials promotes the checked primitive norm
identity; no source-form premise is needed. -/
theorem re_inner_suzukiSourceKOperator_nonneg
    {a : Real} (ha : 0 < a) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    0 <= (inner Complex (suzukiSourceKOperator a u) u).re := by
  let p : SuzukiFiniteIntervalZeroMeanL2 a -> Prop := fun w =>
    0 <= (inner Complex (suzukiSourceKOperator a w) w).re
  apply DenseRange.induction_on (p := p)
    (suzukiSmoothDifferentialCoreDenseAt a ha) u
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro v
    dsimp only [p]
    unfold suzukiSmoothCoreDifferentialZeroMeanL2
    rw [inner_suzukiSourceKOperator_smoothCoreDifferential_eq_norm_sq ha v]
    change 0 <= ‖suzukiSmoothCoreToL2 v‖ ^ 2
    positivity

/-- Positivity of the exact compressed inverse-Neumann source operator. -/
theorem suzukiSourceKOperator_isPositive
    {a : Real} (ha : 0 < a) :
    ContinuousLinearMap.IsPositive (suzukiSourceKOperator a) := by
  rw [ContinuousLinearMap.isPositive_def']
  exact ⟨suzukiSourceKOperator_isSelfAdjoint a,
    re_inner_suzukiSourceKOperator_nonneg ha⟩

/-- The source seminorm induced by Suzuki's positive inverse-Neumann
operator `K_a`. -/
def suzukiSourceKSeminorm
    (a : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) : Real :=
  Real.sqrt (inner Complex (suzukiSourceKOperator a u) u).re

theorem suzukiSourceKSeminorm_nonneg
    (a : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    0 <= suzukiSourceKSeminorm a u :=
  Real.sqrt_nonneg _

theorem suzukiSourceKSeminorm_sq
    {a : Real} (ha : 0 < a) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    suzukiSourceKSeminorm a u ^ 2 =
      (inner Complex (suzukiSourceKOperator a u) u).re := by
  exact Real.sq_sqrt (re_inner_suzukiSourceKOperator_nonneg ha u)

/-- Cauchy--Schwarz for the positive `K_a` form. -/
theorem norm_inner_suzukiSourceKOperator_le
    {a : Real} (ha : 0 < a)
    (u v : SuzukiFiniteIntervalZeroMeanL2 a) :
    ‖inner Complex (suzukiSourceKOperator a u) v‖ <=
      suzukiSourceKSeminorm a u * suzukiSourceKSeminorm a v := by
  let c : PreInnerProductSpace.Core Complex
      (SuzukiFiniteIntervalZeroMeanL2 a) := {
    inner := fun x y => inner Complex (suzukiSourceKOperator a x) y
    conj_inner_symm := fun x y => by
      calc
        conj (inner Complex (suzukiSourceKOperator a y) x) =
            inner Complex x (suzukiSourceKOperator a y) :=
          inner_conj_symm x (suzukiSourceKOperator a y)
        _ = inner Complex (suzukiSourceKOperator a x) y :=
          (suzukiSourceKOperator_isSelfAdjoint a).isSymmetric x y |>.symm
    re_inner_nonneg := re_inner_suzukiSourceKOperator_nonneg ha
    add_left := fun x y z => by
      rw [map_add, inner_add_left]
    smul_left := fun x y r => by
      rw [map_smul]
      exact inner_smul_left (𝕜 := Complex)
        (suzukiSourceKOperator a x) y r }
  have hcs := @InnerProductSpace.Core.inner_mul_inner_self_le
    Complex (SuzukiFiniteIntervalZeroMeanL2 a) _ _ _ c u v
  change
    ‖inner Complex (suzukiSourceKOperator a u) v‖ *
        ‖inner Complex (suzukiSourceKOperator a v) u‖ <=
      (inner Complex (suzukiSourceKOperator a u) u).re *
        (inner Complex (suzukiSourceKOperator a v) v).re at hcs
  have hnormSymm :
      ‖inner Complex (suzukiSourceKOperator a v) u‖ =
        ‖inner Complex (suzukiSourceKOperator a u) v‖ := by
    calc
      ‖inner Complex (suzukiSourceKOperator a v) u‖ =
          ‖inner Complex v (suzukiSourceKOperator a u)‖ :=
        congrArg norm
          ((suzukiSourceKOperator_isSelfAdjoint a).isSymmetric v u)
      _ = ‖inner Complex (suzukiSourceKOperator a u) v‖ :=
        norm_inner_symm v (suzukiSourceKOperator a u)
  rw [hnormSymm] at hcs
  have hsqrt := Real.sqrt_le_sqrt hcs
  rw [Real.sqrt_mul_self (norm_nonneg _),
    Real.sqrt_mul (re_inner_suzukiSourceKOperator_nonneg ha u)] at hsqrt
  exact hsqrt

/-- Vanishing of the inverse-Neumann source seminorm is exactly membership in
the kernel of `K_a`.  Thus the remaining definiteness question is the concrete
injectivity of the compressed source operator, rather than an additional
quadratic-form issue. -/
theorem suzukiSourceKSeminorm_eq_zero_iff
    {a : Real} (ha : 0 < a) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    suzukiSourceKSeminorm a u = 0 ↔ suzukiSourceKOperator a u = 0 := by
  constructor
  · intro hseminorm
    rw [← inner_self_eq_zero (𝕜 := Complex)]
    apply norm_eq_zero.mp
    apply le_antisymm
    · calc
        ‖inner Complex (suzukiSourceKOperator a u)
            (suzukiSourceKOperator a u)‖ <=
            suzukiSourceKSeminorm a u *
              suzukiSourceKSeminorm a (suzukiSourceKOperator a u) :=
          norm_inner_suzukiSourceKOperator_le ha u
            (suzukiSourceKOperator a u)
        _ = 0 := by rw [hseminorm, zero_mul]
    · exact norm_nonneg _
  · intro hoperator
    unfold suzukiSourceKSeminorm
    rw [hoperator, inner_zero_left, Complex.zero_re, Real.sqrt_zero]

/-- Definiteness of the source seminorm is equivalent to injectivity of the
compressed inverse-Neumann operator. -/
theorem suzukiSourceKSeminorm_definite_iff_injective
    {a : Real} (ha : 0 < a) :
    (∀ u : SuzukiFiniteIntervalZeroMeanL2 a,
        suzukiSourceKSeminorm a u = 0 → u = 0) ↔
      Function.Injective (suzukiSourceKOperator a) := by
  constructor
  · intro hdefinite u v huv
    apply sub_eq_zero.mp
    apply hdefinite
    rw [suzukiSourceKSeminorm_eq_zero_iff ha, map_sub, huv, sub_self]
  · intro hinjective u hseminorm
    apply hinjective
    rw [map_zero]
    exact (suzukiSourceKSeminorm_eq_zero_iff ha u).mp hseminorm

/-- Square root of the shifted source energy.  It becomes a genuine norm only
after the relevant representation and definiteness statements are supplied;
this module uses only its checked quantitative comparison with the `K_a`
source seminorm. -/
def suzukiSourceShiftedSeminorm
    (a lambda : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) : Real :=
  Real.sqrt
    (inner Complex (suzukiSourceShiftedOperator a lambda u) u).re

/-- On the DF6E window, every shift strictly below the checked lower endpoint
has nonnegative shifted source energy. -/
theorem re_inner_suzukiSourceShiftedOperator_nonneg
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    0 <=
      (inner Complex (suzukiSourceShiftedOperator a lambda u) u).re := by
  have hc : 0 <= (1 / 400000 : Real) - lambda := by
    linarith
  exact (mul_nonneg hc
      (re_inner_suzukiSourceKOperator_nonneg
        (suzukiDF6E_radius_pos ha) u)).trans
    (suzukiDF6F_interval_shifted_source_coercive
      hsource hequation25 ha lambda u)

/-- Exact square identity for the shifted source-energy seminorm on the
checked window. -/
theorem suzukiSourceShiftedSeminorm_sq
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    suzukiSourceShiftedSeminorm a lambda u ^ 2 =
      (inner Complex (suzukiSourceShiftedOperator a lambda u) u).re := by
  exact Real.sq_sqrt
    (re_inner_suzukiSourceShiftedOperator_nonneg
      hsource hequation25 ha hlambda u)

/-- The precise source-norm embedding supplied by DF6F: shifted source energy
controls the inverse-Neumann source seminorm uniformly at every radius in the
named compact window. -/
theorem suzukiDF6F_sourceKSeminorm_le_shiftedSeminorm
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    Real.sqrt ((1 / 400000 : Real) - lambda) *
        suzukiSourceKSeminorm a u <=
      suzukiSourceShiftedSeminorm a lambda u := by
  have hc : 0 <= (1 / 400000 : Real) - lambda := by
    linarith
  have hcoercive := suzukiDF6F_interval_shifted_source_coercive
    hsource hequation25 ha lambda u
  have hsqrt := Real.sqrt_le_sqrt hcoercive
  rw [Real.sqrt_mul hc] at hsqrt
  exact hsqrt

/-- The `lambda = 0` source-norm consequence permitted on the proved DF6E
window.  No all-radius choice of zero shift is asserted. -/
theorem suzukiDF6F_sourceKSeminorm_le_sourceGSeminorm
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    Real.sqrt (1 / 400000 : Real) * suzukiSourceKSeminorm a u <=
      Real.sqrt (inner Complex (suzukiSourceGOperator a u) u).re := by
  have hzero : (0 : Real) < (1 / 400000 : Real) := by norm_num
  simpa [suzukiSourceShiftedSeminorm, suzukiSourceShiftedOperator] using
    (suzukiDF6F_sourceKSeminorm_le_shiftedSeminorm
      hsource hequation25 ha hzero u)

/-- A forcing vector has source-dual bound `C` when its ambient pairing is
controlled by the `K_a` source seminorm.  This is the precise additional input
needed to turn source coercivity into a solution estimate. -/
def SuzukiSourceKDualBoundAt
    (a : Real) (f : SuzukiFiniteIntervalZeroMeanL2 a) (C : Real) : Prop :=
  forall u : SuzukiFiniteIntervalZeroMeanL2 a,
    ‖inner Complex f u‖ <= C * suzukiSourceKSeminorm a u

/-- Every vector in the range of `K_a` has the expected source-dual bound,
with constant equal to the `K_a` seminorm of its preimage. -/
theorem suzukiSourceKDualBoundAt_operator_apply
    {a : Real} (ha : 0 < a)
    (w : SuzukiFiniteIntervalZeroMeanL2 a) :
    SuzukiSourceKDualBoundAt a (suzukiSourceKOperator a w)
      (suzukiSourceKSeminorm a w) := by
  intro u
  exact norm_inner_suzukiSourceKOperator_le ha w u

/-- The DF6F shifted comparison gives a quantitative source-seminorm bound
for every solution of the source equation.  This is deliberately a solution
estimate rather than a false ambient bounded inverse for the compact operator.
-/
theorem suzukiDF6F_sourceKSeminorm_solution_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda C : Real} (hlambda : lambda < (1 / 400000 : Real))
    (hC : 0 <= C)
    {f u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hdual : SuzukiSourceKDualBoundAt a f C)
    (hsolve : suzukiSourceShiftedOperator a lambda u = f) :
    suzukiSourceKSeminorm a u <=
      C / ((1 / 400000 : Real) - lambda) := by
  have hc : 0 < (1 / 400000 : Real) - lambda := by
    linarith
  have henergy := suzukiDF6F_interval_shifted_source_coercive
    hsource hequation25 ha lambda u
  rw [hsolve] at henergy
  have hdualU := hdual u
  have hre : (inner Complex f u).re <=
      C * suzukiSourceKSeminorm a u :=
    (Complex.re_le_norm _).trans hdualU
  have hsquare :
      ((1 / 400000 : Real) - lambda) *
          suzukiSourceKSeminorm a u ^ 2 <=
        C * suzukiSourceKSeminorm a u := by
    rw [suzukiSourceKSeminorm_sq (suzukiDF6E_radius_pos ha)]
    exact henergy.trans hre
  have hu : 0 <= suzukiSourceKSeminorm a u :=
    suzukiSourceKSeminorm_nonneg a u
  apply (le_div_iff₀ hc).2
  by_cases hzero : suzukiSourceKSeminorm a u = 0
  · simpa [hzero] using hC
  · have hupos : 0 < suzukiSourceKSeminorm a u :=
      lt_of_le_of_ne hu (Ne.symm hzero)
    nlinarith

/-- Direct range-of-`K_a` forcing specialization of the shifted solution
estimate. -/
theorem suzukiDF6F_sourceKOperator_forcing_solution_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (w : SuzukiFiniteIntervalZeroMeanL2 a)
    (hsolve : suzukiSourceShiftedOperator a lambda u =
      suzukiSourceKOperator a w) :
    suzukiSourceKSeminorm a u <=
      suzukiSourceKSeminorm a w /
        ((1 / 400000 : Real) - lambda) := by
  exact suzukiDF6F_sourceKSeminorm_solution_le
    hsource hequation25 ha hlambda
    (suzukiSourceKSeminorm_nonneg a w)
    (suzukiSourceKDualBoundAt_operator_apply
      (suzukiDF6E_radius_pos ha) w) hsolve

/-- Zero-shift specialization on the named interval.  A uniform source-dual
bound `C` for a forcing family gives the explicit uniform solution bound
`400000 * C`. -/
theorem suzukiDF6F_sourceG_solution_sourceKSeminorm_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {C : Real} (hC : 0 <= C)
    {f u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hdual : SuzukiSourceKDualBoundAt a f C)
    (hsolve : suzukiSourceGOperator a u = f) :
    suzukiSourceKSeminorm a u <= 400000 * C := by
  have hzero : (0 : Real) < (1 / 400000 : Real) := by norm_num
  have hsolveZero : suzukiSourceShiftedOperator a 0 u = f := by
    simpa [suzukiSourceShiftedOperator] using hsolve
  have hbound := suzukiDF6F_sourceKSeminorm_solution_le
    hsource hequation25 ha hzero hC hdual hsolveZero
  calc
    suzukiSourceKSeminorm a u <=
        C / ((1 / 400000 : Real) - 0) := hbound
    _ = 400000 * C := by norm_num; ring

/-- Zero-shift range-of-`K_a` forcing specialization, with no ambient inverse
claim. -/
theorem suzukiDF6F_sourceG_KOperator_forcing_solution_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (w : SuzukiFiniteIntervalZeroMeanL2 a)
    (hsolve : suzukiSourceGOperator a u = suzukiSourceKOperator a w) :
    suzukiSourceKSeminorm a u <=
      400000 * suzukiSourceKSeminorm a w := by
  exact suzukiDF6F_sourceG_solution_sourceKSeminorm_le
    hsource hequation25 ha (suzukiSourceKSeminorm_nonneg a w)
    (suzukiSourceKDualBoundAt_operator_apply
      (suzukiDF6E_radius_pos ha) w) hsolve

end

end RiemannHypothesisProject.Experiments.M100
