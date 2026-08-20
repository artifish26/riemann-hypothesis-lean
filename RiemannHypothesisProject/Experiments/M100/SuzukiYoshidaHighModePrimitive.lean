import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaNegativeWeightLoss
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Cutoff-44 high-mode primitives for M100-DF6D5B3F-F

This module constructs the endpoint-zero primitive of a finite linear
combination of the cutoff-44 Yoshida exponentials.  The primitive splits into
an orthogonal high-mode multiplier and a constant endpoint correction.  The
two estimates are respectively controlled by the smallest high frequency
`45` and by the already checked two-sided reciprocal-square tail `2 / 44`.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped ComplexConjugate InnerProductSpace

/-- The Fourier multiplier which integrates physical mode `-j` once. -/
def cutoff44HighPrimitiveMultiplier (j : Cutoff44HighIndex) : Complex :=
  Complex.I *
    ((suzukiProjectAStar / ((j.1 : Real) * Real.pi) : Real) : Complex)

/-- The value at the left endpoint of physical mode `-j`, relative to the
normalized constant mode. -/
def cutoff44HighEndpointPhase (j : Cutoff44HighIndex) : Complex :=
  ((j.1.negOnePow : Int) : Complex)

theorem cutoff44HighIndex_abs_ge_45 (j : Cutoff44HighIndex) :
    (45 : Real) ≤ |(j.1 : Real)| := by
  have hjCases : j.1 < -44 ∨ 44 < j.1 := by
    simpa only [Finset.mem_Icc, not_and_or, not_le] using j.2
  rcases hjCases with hj | hj
  · rw [abs_of_nonpos]
    · exact_mod_cast (show (45 : Int) ≤ -j.1 by omega)
    · exact_mod_cast (show j.1 ≤ 0 by omega)
  · rw [abs_of_nonneg]
    · exact_mod_cast (show (45 : Int) ≤ j.1 by omega)
    · exact_mod_cast (show (0 : Int) ≤ j.1 by omega)

theorem cutoff44HighIndex_ne_zero (j : Cutoff44HighIndex) :
    j.1 ≠ 0 := by
  intro hj
  apply j.2
  simp [hj]

@[simp]
theorem norm_cutoff44HighEndpointPhase (j : Cutoff44HighIndex) :
    ‖cutoff44HighEndpointPhase j‖ = 1 := by
  unfold cutoff44HighEndpointPhase
  rw [Complex.norm_intCast]
  exact_mod_cast Int.abs_negOnePow j.1

theorem norm_sq_cutoff44HighPrimitiveMultiplier
    (j : Cutoff44HighIndex) :
    ‖cutoff44HighPrimitiveMultiplier j‖ ^ 2 =
      (suzukiProjectAStar / Real.pi) ^ 2 *
        (1 / (j.1 : Real) ^ 2) := by
  have hj0 : (j.1 : Real) ≠ 0 := by
    exact_mod_cast cutoff44HighIndex_ne_zero j
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold cutoff44HighPrimitiveMultiplier
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos suzukiProjectAStar_pos, abs_of_pos Real.pi_pos]
  rw [div_pow]
  field_simp
  rw [sq_abs]

theorem cutoff44HighPrimitiveMultiplier_ne_zero
    (j : Cutoff44HighIndex) :
    cutoff44HighPrimitiveMultiplier j ≠ 0 := by
  unfold cutoff44HighPrimitiveMultiplier
  apply mul_ne_zero Complex.I_ne_zero
  have hj0 : (j.1 : Real) ≠ 0 := by
    exact_mod_cast cutoff44HighIndex_ne_zero j
  exact_mod_cast div_ne_zero suzukiProjectAStar_pos.ne'
    (mul_ne_zero hj0 Real.pi_ne_zero)

/-- Coefficients of the periodic part of the primitive. -/
def cutoff44HighPrimitiveCoefficients
    (l : Cutoff44HighIndex →₀ Complex) :
    Cutoff44HighIndex →₀ Complex :=
  Finsupp.onFinset l.support
    (fun j => l j * cutoff44HighPrimitiveMultiplier j)
    (by
      intro j hj
      by_contra hmem
      rw [Finsupp.notMem_support_iff.mp hmem, zero_mul] at hj
      exact hj rfl)

@[simp]
theorem cutoff44HighPrimitiveCoefficients_apply
    (l : Cutoff44HighIndex →₀ Complex) (j : Cutoff44HighIndex) :
    cutoff44HighPrimitiveCoefficients l j =
      l j * cutoff44HighPrimitiveMultiplier j := by
  exact Finsupp.onFinset_apply

theorem cutoff44HighPrimitiveCoefficients_support
    (l : Cutoff44HighIndex →₀ Complex) :
    (cutoff44HighPrimitiveCoefficients l).support = l.support := by
  ext j
  simp only [Finsupp.mem_support_iff,
    cutoff44HighPrimitiveCoefficients_apply]
  constructor
  · intro h hzero
    exact h (by rw [hzero, zero_mul])
  · intro h
    exact mul_ne_zero h (cutoff44HighPrimitiveMultiplier_ne_zero j)

/-- The high-mode (periodic) part of the endpoint-zero primitive. -/
def cutoff44HighPeriodicPrimitive
    (l : Cutoff44HighIndex →₀ Complex) : SuzukiL2 :=
  Finsupp.linearCombination Complex cutoff44HighExponential
    (cutoff44HighPrimitiveCoefficients l)

theorem norm_sq_cutoff44HighPeriodicPrimitive_le
    (l : Cutoff44HighIndex →₀ Complex) :
    ‖cutoff44HighPeriodicPrimitive l‖ ^ 2 ≤
      (suzukiProjectAStar / Real.pi) ^ 2 * (1 / 45 ^ 2) *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 := by
  rw [cutoff44HighPeriodicPrimitive,
    norm_sq_cutoff44HighExponential_linearCombination,
    norm_sq_cutoff44HighExponential_linearCombination]
  let C : Real := (suzukiProjectAStar / Real.pi) ^ 2 * (1 / 45 ^ 2)
  calc
    (cutoff44HighPrimitiveCoefficients l).sum (fun _ c => ‖c‖ ^ 2) =
        ∑ j ∈ l.support,
          ‖l j * cutoff44HighPrimitiveMultiplier j‖ ^ 2 := by
      rw [Finsupp.sum, cutoff44HighPrimitiveCoefficients_support]
      apply Finset.sum_congr rfl
      intro j hj
      rw [cutoff44HighPrimitiveCoefficients_apply]
    _ ≤ ∑ j ∈ l.support, C * ‖l j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, mul_pow, norm_sq_cutoff44HighPrimitiveMultiplier]
      have hjSq : (45 : Real) ^ 2 ≤ (j.1 : Real) ^ 2 := by
        have habsSq :=
          (sq_le_sq₀ (by norm_num : (0 : Real) ≤ 45)
            (abs_nonneg (j.1 : Real))).2
              (cutoff44HighIndex_abs_ge_45 j)
        simpa only [sq_abs] using habsSq
      have hrecip : 1 / (j.1 : Real) ^ 2 ≤ (1 / 45 ^ 2 : Real) := by
        exact one_div_le_one_div_of_le (by norm_num) hjSq
      dsimp only [C]
      have hscale : 0 ≤ (suzukiProjectAStar / Real.pi) ^ 2 := sq_nonneg _
      calc
        ‖l j‖ ^ 2 *
            ((suzukiProjectAStar / Real.pi) ^ 2 *
              (1 / (j.1 : Real) ^ 2)) ≤
            ‖l j‖ ^ 2 *
              ((suzukiProjectAStar / Real.pi) ^ 2 * (1 / 45 ^ 2)) := by
          gcongr
        _ = (suzukiProjectAStar / Real.pi) ^ 2 * (1 / 45 ^ 2) *
            ‖l j‖ ^ 2 := by ring
    _ = C * l.sum (fun _ c => ‖c‖ ^ 2) := by
      rw [Finsupp.sum, Finset.mul_sum]
    _ = (suzukiProjectAStar / Real.pi) ^ 2 * (1 / 45 ^ 2) *
        l.sum (fun _ c => ‖c‖ ^ 2) := rfl

/-- Coefficient of the normalized constant mode in the endpoint correction. -/
def cutoff44HighPrimitiveEndpointCoefficient
    (l : Cutoff44HighIndex →₀ Complex) : Complex :=
  l.sum fun j c =>
    c * cutoff44HighPrimitiveMultiplier j * cutoff44HighEndpointPhase j

theorem norm_sq_cutoff44HighPrimitiveEndpointCoefficient_le
    (l : Cutoff44HighIndex →₀ Complex) :
    ‖cutoff44HighPrimitiveEndpointCoefficient l‖ ^ 2 ≤
      (suzukiProjectAStar / Real.pi) ^ 2 * (2 / 44) *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 := by
  have hrecip : Summable (fun j : Cutoff44HighIndex =>
      1 / (j.1 : Real) ^ 2) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).subtype _
  have hfinite :
      (∑ j ∈ l.support, 1 / (j.1 : Real) ^ 2) ≤
        ∑' j : Cutoff44HighIndex, 1 / (j.1 : Real) ^ 2 :=
    hrecip.sum_le_tsum l.support (fun j hj => by positivity)
  have hscale : 0 ≤ (suzukiProjectAStar / Real.pi) ^ 2 := sq_nonneg _
  have hweights :
      (∑ j ∈ l.support,
          ‖cutoff44HighPrimitiveMultiplier j *
            cutoff44HighEndpointPhase j‖ ^ 2) ≤
        (suzukiProjectAStar / Real.pi) ^ 2 * (2 / 44) := by
    calc
      (∑ j ∈ l.support,
          ‖cutoff44HighPrimitiveMultiplier j *
            cutoff44HighEndpointPhase j‖ ^ 2) =
          (suzukiProjectAStar / Real.pi) ^ 2 *
            ∑ j ∈ l.support, 1 / (j.1 : Real) ^ 2 := by
        simp_rw [norm_mul, norm_cutoff44HighEndpointPhase, mul_one,
          norm_sq_cutoff44HighPrimitiveMultiplier]
        rw [Finset.mul_sum]
      _ ≤ (suzukiProjectAStar / Real.pi) ^ 2 *
          (∑' j : Cutoff44HighIndex, 1 / (j.1 : Real) ^ 2) :=
        mul_le_mul_of_nonneg_left hfinite hscale
      _ ≤ (suzukiProjectAStar / Real.pi) ^ 2 * (2 / 44) :=
        mul_le_mul_of_nonneg_left
          cutoff44HighIndex_reciprocal_sq_tsum_le hscale
  have hcs := norm_finset_sum_mul_sq_le l.support
    (fun j => l j)
    (fun j => cutoff44HighPrimitiveMultiplier j *
      cutoff44HighEndpointPhase j)
  rw [cutoff44HighPrimitiveEndpointCoefficient, Finsupp.sum]
  simp_rw [mul_assoc]
  apply hcs.trans
  rw [norm_sq_cutoff44HighExponential_linearCombination]
  have hcoeff : 0 ≤ ∑ j ∈ l.support, ‖l j‖ ^ 2 :=
    Finset.sum_nonneg fun j hj => sq_nonneg _
  calc
    (∑ j ∈ l.support, ‖l j‖ ^ 2) *
        (∑ j ∈ l.support,
          ‖cutoff44HighPrimitiveMultiplier j *
            cutoff44HighEndpointPhase j‖ ^ 2) ≤
        (∑ j ∈ l.support, ‖l j‖ ^ 2) *
          ((suzukiProjectAStar / Real.pi) ^ 2 * (2 / 44)) :=
      mul_le_mul_of_nonneg_left hweights hcoeff
    _ = (suzukiProjectAStar / Real.pi) ^ 2 *
        ((2 / 44) * l.sum (fun _ c => ‖c‖ ^ 2)) := by
      rw [Finsupp.sum]
      ring

/-- The endpoint-zero primitive of a finite cutoff-44 Fourier combination. -/
def cutoff44HighEndpointPrimitive
    (l : Cutoff44HighIndex →₀ Complex) : SuzukiL2 :=
  cutoff44HighPeriodicPrimitive l -
    cutoff44HighPrimitiveEndpointCoefficient l •
      suzukiYoshidaExponentialL2 suzukiProjectAStar
        suzukiProjectAStar_pos 0

/-- The single-mode endpoint-zero primitive. -/
def cutoff44HighEndpointPrimitiveMode
    (j : Cutoff44HighIndex) : SuzukiL2 :=
  cutoff44HighPrimitiveMultiplier j •
    (cutoff44HighExponential j -
      cutoff44HighEndpointPhase j •
        suzukiYoshidaExponentialL2 suzukiProjectAStar
          suzukiProjectAStar_pos 0)

/-- The finite high-mode primitive as an honest linear map on coefficients. -/
def cutoff44HighEndpointPrimitiveLinearMap :
    (Cutoff44HighIndex →₀ Complex) →ₗ[Complex] SuzukiL2 :=
  Finsupp.linearCombination Complex cutoff44HighEndpointPrimitiveMode

theorem cutoff44HighEndpointPrimitiveLinearMap_apply
    (l : Cutoff44HighIndex →₀ Complex) :
    cutoff44HighEndpointPrimitiveLinearMap l =
      cutoff44HighEndpointPrimitive l := by
  rw [cutoff44HighEndpointPrimitiveLinearMap,
    Finsupp.linearCombination_apply]
  unfold cutoff44HighEndpointPrimitive
  rw [cutoff44HighPeriodicPrimitive, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum,
    cutoff44HighPrimitiveCoefficients_support,
    cutoff44HighPrimitiveCoefficients_apply,
    cutoff44HighPrimitiveEndpointCoefficient,
    cutoff44HighEndpointPrimitiveMode,
    smul_sub, smul_smul, Finset.sum_sub_distrib,
    Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc]

theorem inner_cutoff44HighPeriodicPrimitive_constant
    (l : Cutoff44HighIndex →₀ Complex) :
    inner Complex (cutoff44HighPeriodicPrimitive l)
      (suzukiYoshidaExponentialL2 suzukiProjectAStar
        suzukiProjectAStar_pos 0) = 0 := by
  have hortho := orthonormal_iff_ite.mp
    (orthonormal_suzukiYoshidaExponentialL2 suzukiProjectAStar_pos)
  rw [cutoff44HighPeriodicPrimitive, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, sum_inner, inner_smul_left]
  apply Finset.sum_eq_zero
  intro j hj
  have hmode : (-j.1 : Int) ≠ 0 := by
    intro h
    exact cutoff44HighIndex_ne_zero j (neg_eq_zero.mp h)
  have hinner := hortho (-j.1) 0
  rw [if_neg hmode] at hinner
  rw [cutoff44HighExponential, hinner, mul_zero]

theorem norm_sq_cutoff44HighEndpointPrimitive_eq
    (l : Cutoff44HighIndex →₀ Complex) :
    ‖cutoff44HighEndpointPrimitive l‖ ^ 2 =
      ‖cutoff44HighPeriodicPrimitive l‖ ^ 2 +
        ‖cutoff44HighPrimitiveEndpointCoefficient l‖ ^ 2 := by
  have hinner : inner Complex (cutoff44HighPeriodicPrimitive l)
      (-(cutoff44HighPrimitiveEndpointCoefficient l •
      suzukiYoshidaExponentialL2 suzukiProjectAStar
          suzukiProjectAStar_pos 0)) = 0 := by
    rw [inner_neg_right, inner_smul_right,
      inner_cutoff44HighPeriodicPrimitive_constant]
    simp
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (cutoff44HighPeriodicPrimitive l)
    (-(cutoff44HighPrimitiveEndpointCoefficient l •
      suzukiYoshidaExponentialL2 suzukiProjectAStar
        suzukiProjectAStar_pos 0)) hinner
  rw [norm_neg, norm_smul,
    (orthonormal_suzukiYoshidaExponentialL2
      suzukiProjectAStar_pos).norm_eq_one,
    mul_one] at hpyth
  simpa only [cutoff44HighEndpointPrimitive, sub_eq_add_neg, pow_two]
    using hpyth

theorem norm_sq_cutoff44HighEndpointPrimitive_le
    (l : Cutoff44HighIndex →₀ Complex) :
    ‖cutoff44HighEndpointPrimitive l‖ ^ 2 ≤
      (suzukiProjectAStar / Real.pi) ^ 2 *
        (2047 / 44550) *
          ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 := by
  rw [norm_sq_cutoff44HighEndpointPrimitive_eq]
  have hperiodic := norm_sq_cutoff44HighPeriodicPrimitive_le l
  have hendpoint :=
    norm_sq_cutoff44HighPrimitiveEndpointCoefficient_le l
  calc
    ‖cutoff44HighPeriodicPrimitive l‖ ^ 2 +
        ‖cutoff44HighPrimitiveEndpointCoefficient l‖ ^ 2 ≤
      ((suzukiProjectAStar / Real.pi) ^ 2 * (1 / 45 ^ 2) +
        (suzukiProjectAStar / Real.pi) ^ 2 * (2 / 44)) *
          ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 := by
      nlinarith [sq_nonneg
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖]
    _ = (suzukiProjectAStar / Real.pi) ^ 2 *
        (2047 / 44550) *
          ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 := by
      ring

theorem suzukiDF6D4DF0PrimitiveNorm_sq :
    suzukiDF6D4DF0PrimitiveNorm ^ 2 =
      (suzukiProjectAStar / Real.pi) ^ 2 * (2047 / 44550) := by
  have hratio : (0 : Real) ≤ 2047 / 44550 := by norm_num
  unfold suzukiDF6D4DF0PrimitiveNorm
  rw [mul_pow, Real.sq_sqrt hratio]
  ring

theorem suzukiDF6D4DF0PrimitiveNorm_nonneg :
    0 ≤ suzukiDF6D4DF0PrimitiveNorm := by
  unfold suzukiDF6D4DF0PrimitiveNorm
  exact mul_nonneg
    (mul_nonneg suzukiProjectAStar_pos.le
      (inv_nonneg.mpr Real.pi_pos.le))
    (Real.sqrt_nonneg _)

/-- The exact DF0 primitive norm bound on every finite cutoff-44 Fourier
combination. -/
theorem norm_cutoff44HighEndpointPrimitive_le_DF0
    (l : Cutoff44HighIndex →₀ Complex) :
    ‖cutoff44HighEndpointPrimitive l‖ ≤
      suzukiDF6D4DF0PrimitiveNorm *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg suzukiDF6D4DF0PrimitiveNorm_nonneg (norm_nonneg _))).mp
  rw [mul_pow, suzukiDF6D4DF0PrimitiveNorm_sq]
  exact norm_sq_cutoff44HighEndpointPrimitive_le l

/-- The primitive transported from Fourier coefficients to the algebraic
high-mode subspace. -/
theorem linearIndependent_cutoff44HighExponential :
    LinearIndependent Complex cutoff44HighExponential :=
  orthonormal_cutoff44HighExponential.linearIndependent

def cutoff44HighSubspacePrimitiveLinearMap :
    cutoff44HighExponentialSubspace →ₗ[Complex] SuzukiL2 :=
  cutoff44HighEndpointPrimitiveLinearMap.comp
    linearIndependent_cutoff44HighExponential.repr

theorem cutoff44HighSubspacePrimitiveLinearMap_apply
    (v : cutoff44HighExponentialSubspace) :
    cutoff44HighSubspacePrimitiveLinearMap v =
      cutoff44HighEndpointPrimitive
        (linearIndependent_cutoff44HighExponential.repr v) := by
  rw [cutoff44HighSubspacePrimitiveLinearMap, LinearMap.comp_apply,
    cutoff44HighEndpointPrimitiveLinearMap_apply]
  rfl

theorem norm_cutoff44HighSubspacePrimitiveLinearMap_le
    (v : cutoff44HighExponentialSubspace) :
    ‖cutoff44HighSubspacePrimitiveLinearMap v‖ ≤
      suzukiDF6D4DF0PrimitiveNorm * ‖v‖ := by
  let l : Cutoff44HighIndex →₀ Complex :=
    linearIndependent_cutoff44HighExponential.repr v
  have hrepr :=
    linearIndependent_cutoff44HighExponential.linearCombination_repr v
  have hbound := norm_cutoff44HighEndpointPrimitive_le_DF0 l
  rw [cutoff44HighSubspacePrimitiveLinearMap_apply]
  change ‖cutoff44HighEndpointPrimitive l‖ ≤ _
  change Finsupp.linearCombination Complex cutoff44HighExponential l = v.1 at hrepr
  rw [hrepr] at hbound
  exact hbound

/-- The bounded primitive on the algebraic high-mode subspace. -/
def cutoff44HighSubspacePrimitive :
    cutoff44HighExponentialSubspace →L[Complex] SuzukiL2 :=
  cutoff44HighSubspacePrimitiveLinearMap.mkContinuous
    suzukiDF6D4DF0PrimitiveNorm
    norm_cutoff44HighSubspacePrimitiveLinearMap_le

theorem norm_cutoff44HighSubspacePrimitive_le
    (v : cutoff44HighExponentialSubspace) :
    ‖cutoff44HighSubspacePrimitive v‖ ≤
      suzukiDF6D4DF0PrimitiveNorm * ‖v‖ :=
  norm_cutoff44HighSubspacePrimitiveLinearMap_le v

/-- Isometric inclusion of the algebraic high-mode subspace into its closed
completion. -/
def cutoff44HighSubspaceClosureInclusion :
    cutoff44HighExponentialSubspace →ₗᵢ[Complex]
      cutoff44HighExponentialSubspace.topologicalClosure where
  toLinearMap := Submodule.inclusion
    cutoff44HighExponentialSubspace.le_topologicalClosure
  norm_map' := fun _ => rfl

theorem cutoff44HighSubspaceClosureInclusion_denseRange :
    DenseRange cutoff44HighSubspaceClosureInclusion := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hx : x.1 ∈ closure
      (cutoff44HighExponentialSubspace : Set SuzukiL2) := x.2
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hx ε hε
  refine ⟨⟨y, hy⟩, ?_⟩
  change dist x.1 y < ε
  exact hdist

theorem cutoff44HighSubspaceClosureInclusion_isUniformInducing :
    IsUniformInducing
      cutoff44HighSubspaceClosureInclusion.toContinuousLinearMap :=
  cutoff44HighSubspaceClosureInclusion.isometry.isUniformInducing

/-- Continuous primitive on the entire closed cutoff-44 high-mode space. -/
def cutoff44HighClosurePrimitive :
    cutoff44HighExponentialSubspace.topologicalClosure →L[Complex] SuzukiL2 :=
  ContinuousLinearMap.extend cutoff44HighSubspacePrimitive
    cutoff44HighSubspaceClosureInclusion.toContinuousLinearMap

set_option maxHeartbeats 800000 in
theorem cutoff44HighClosurePrimitive_eq_on_subspace
    (v : cutoff44HighExponentialSubspace) :
    cutoff44HighClosurePrimitive (cutoff44HighSubspaceClosureInclusion v) =
      cutoff44HighSubspacePrimitive v := by
  apply ContinuousLinearMap.extend_eq
    cutoff44HighSubspacePrimitive
    cutoff44HighSubspaceClosureInclusion_denseRange
    cutoff44HighSubspaceClosureInclusion_isUniformInducing

set_option maxHeartbeats 800000 in
theorem norm_cutoff44HighClosurePrimitive_le_DF0
    (v : cutoff44HighExponentialSubspace.topologicalClosure) :
    ‖cutoff44HighClosurePrimitive v‖ ≤
      suzukiDF6D4DF0PrimitiveNorm * ‖v‖ := by
  let p : cutoff44HighExponentialSubspace.topologicalClosure → Prop :=
    fun w => ‖cutoff44HighClosurePrimitive w‖ ≤
      suzukiDF6D4DF0PrimitiveNorm * ‖w‖
  apply DenseRange.induction_on
    (p := p) cutoff44HighSubspaceClosureInclusion_denseRange v
  · exact isClosed_le
      (continuous_norm.comp cutoff44HighClosurePrimitive.continuous)
      (continuous_const.mul continuous_norm)
  · intro w
    dsimp only [p]
    rw [cutoff44HighClosurePrimitive_eq_on_subspace]
    exact norm_cutoff44HighSubspacePrimitive_le w

/-- Every vector in either ambient parity tail has a canonical cutoff-44
primitive with the exact DF0 norm bound. -/
theorem exists_cutoff44HighPrimitive_of_mem_ambientFar
    (v : SuzukiL2)
    (hv : v ∈ suzukiDF6D5B3TEvenAmbientFarSubspace ∨
      v ∈ suzukiDF6D5B3TOddAmbientFarSubspace) :
    ∃ H : SuzukiL2,
      ‖H‖ ≤ suzukiDF6D4DF0PrimitiveNorm * ‖v‖ := by
  have hvClosure :
      v ∈ cutoff44HighExponentialSubspace.topologicalClosure := by
    rcases hv with heven | hodd
    · exact suzukiDF6D5B3TEvenAmbientFarSubspace_le_cutoff44HighClosure heven
    · exact suzukiDF6D5B3TOddAmbientFarSubspace_le_cutoff44HighClosure hodd
  let w : cutoff44HighExponentialSubspace.topologicalClosure := ⟨v, hvClosure⟩
  exact ⟨cutoff44HighClosurePrimitive w, by
    simpa only [w, Submodule.coe_norm] using
      norm_cutoff44HighClosurePrimitive_le_DF0 w⟩

/-- Canonical primitive of a vector in the union of the two ambient parity
tails. -/
def cutoff44HighAmbientPrimitive
    (v : SuzukiL2)
    (hv : v ∈ suzukiDF6D5B3TEvenAmbientFarSubspace ∨
      v ∈ suzukiDF6D5B3TOddAmbientFarSubspace) : SuzukiL2 :=
  cutoff44HighClosurePrimitive ⟨v, by
    rcases hv with heven | hodd
    · exact suzukiDF6D5B3TEvenAmbientFarSubspace_le_cutoff44HighClosure heven
    · exact suzukiDF6D5B3TOddAmbientFarSubspace_le_cutoff44HighClosure hodd⟩

theorem norm_cutoff44HighAmbientPrimitive_le_DF0
    (v : SuzukiL2)
    (hv : v ∈ suzukiDF6D5B3TEvenAmbientFarSubspace ∨
      v ∈ suzukiDF6D5B3TOddAmbientFarSubspace) :
    ‖cutoff44HighAmbientPrimitive v hv‖ ≤
      suzukiDF6D4DF0PrimitiveNorm * ‖v‖ := by
  unfold cutoff44HighAmbientPrimitive
  simpa only [Submodule.coe_norm] using
    norm_cutoff44HighClosurePrimitive_le_DF0
      (⟨v, by
        rcases hv with heven | hodd
        · exact suzukiDF6D5B3TEvenAmbientFarSubspace_le_cutoff44HighClosure heven
        · exact suzukiDF6D5B3TOddAmbientFarSubspace_le_cutoff44HighClosure hodd⟩ :
          cutoff44HighExponentialSubspace.topologicalClosure)

end

end RiemannHypothesisProject.Experiments.M100
