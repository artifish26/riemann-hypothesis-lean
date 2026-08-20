import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaResidualModalCoefficients
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Parseval for the B3R-E ambient residual representers

This module packages the physical even and odd Yoshida tail modes as Hilbert
bases of the exact ambient tail subtypes and applies those bases to the actual
E4 residual functionals.  The source hypotheses remain explicit.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped BigOperators ComplexConjugate

set_option maxHeartbeats 0

/-! ## Hilbert bases of the ambient parity tails -/

private theorem suzukiDF6D5B3REvenAmbientMode_orthonormal :
    Orthonormal Complex suzukiDF6D5B3REvenAmbientMode := by
  rw [orthonormal_iff_ite]
  intro i j
  change
    inner Complex
        (suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos i.1)
        (suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos j.1) =
      if i = j then 1 else 0
  rw [inner_suzukiYoshidaEvenL2_eq_ite]
  by_cases hij : i = j
  · simp [hij]
  · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp [hij, hval]

private theorem suzukiDF6D5B3ROddAmbientMode_orthonormal :
    Orthonormal Complex suzukiDF6D5B3ROddAmbientMode := by
  rw [orthonormal_iff_ite]
  intro i j
  change
    inner Complex
        (suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos i.1)
        (suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos j.1) =
      if i = j then 1 else 0
  rw [inner_suzukiYoshidaOddL2_eq_ite
    suzukiProjectAStar_pos (by omega) (by omega)]
  by_cases hij : i = j
  · simp [hij]
  · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp [hij, hval]

private theorem suzukiDF6D5B3REvenAmbientMode_orthogonal_eq_bot :
    (Submodule.span Complex
      (Set.range suzukiDF6D5B3REvenAmbientMode))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  let K : Submodule Complex SuzukiL2 :=
    Submodule.span Complex
      (Set.range fun n : SuzukiDF6D5B3RTailMode =>
        suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos n.1)
  have hvAmbient : (v : SuzukiL2) ∈ K.topologicalClosure := by
    exact v.property
  have hvOrth : (v : SuzukiL2) ∈ K.topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨n, rfl⟩
      have hmode :
          inner Complex (suzukiDF6D5B3REvenAmbientMode n) v = 0 :=
        Submodule.inner_right_of_mem_orthogonal
          (Submodule.subset_span (Set.mem_range_self n)) hv
      exact hmode
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx
      rw [inner_smul_left, hx, mul_zero]
  have hself : inner Complex (v : SuzukiL2) v = 0 :=
    Submodule.inner_right_of_mem_orthogonal hvAmbient hvOrth
  exact Subtype.ext (inner_self_eq_zero.mp hself)

private theorem suzukiDF6D5B3ROddAmbientMode_orthogonal_eq_bot :
    (Submodule.span Complex
      (Set.range suzukiDF6D5B3ROddAmbientMode))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  let K : Submodule Complex SuzukiL2 :=
    Submodule.span Complex
      (Set.range fun n : SuzukiDF6D5B3RTailMode =>
        suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos n.1)
  have hvAmbient : (v : SuzukiL2) ∈ K.topologicalClosure := by
    exact v.property
  have hvOrth : (v : SuzukiL2) ∈ K.topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨n, rfl⟩
      have hmode :
          inner Complex (suzukiDF6D5B3ROddAmbientMode n) v = 0 :=
        Submodule.inner_right_of_mem_orthogonal
          (Submodule.subset_span (Set.mem_range_self n)) hv
      exact hmode
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx
      rw [inner_smul_left, hx, mul_zero]
  have hself : inner Complex (v : SuzukiL2) v = 0 :=
    Submodule.inner_right_of_mem_orthogonal hvAmbient hvOrth
  exact Subtype.ext (inner_self_eq_zero.mp hself)

/-- The physical even modes `n ≥ 45` form a Hilbert basis of the exact even
ambient tail. -/
def suzukiDF6D5B3REvenAmbientHilbertBasis :
    HilbertBasis SuzukiDF6D5B3RTailMode Complex
      SuzukiDF6D5B3REvenAmbientFarL2 := by
  letI : CompleteSpace SuzukiDF6D5B3REvenAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace.completeSpace_coe
  exact HilbertBasis.mkOfOrthogonalEqBot
    suzukiDF6D5B3REvenAmbientMode_orthonormal
    suzukiDF6D5B3REvenAmbientMode_orthogonal_eq_bot

/-- The physical odd modes `n ≥ 45` form a Hilbert basis of the exact odd
ambient tail. -/
def suzukiDF6D5B3ROddAmbientHilbertBasis :
    HilbertBasis SuzukiDF6D5B3RTailMode Complex
      SuzukiDF6D5B3ROddAmbientFarL2 := by
  letI : CompleteSpace SuzukiDF6D5B3ROddAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TOddAmbientFarSubspace.completeSpace_coe
  exact HilbertBasis.mkOfOrthogonalEqBot
    suzukiDF6D5B3ROddAmbientMode_orthonormal
    suzukiDF6D5B3ROddAmbientMode_orthogonal_eq_bot

@[simp]
theorem suzukiDF6D5B3REvenAmbientHilbertBasis_apply
    (n : SuzukiDF6D5B3RTailMode) :
    suzukiDF6D5B3REvenAmbientHilbertBasis n =
      suzukiDF6D5B3REvenAmbientMode n := by
  letI : CompleteSpace SuzukiDF6D5B3REvenAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace.completeSpace_coe
  exact congr_fun (HilbertBasis.coe_mkOfOrthogonalEqBot
    suzukiDF6D5B3REvenAmbientMode_orthonormal
    suzukiDF6D5B3REvenAmbientMode_orthogonal_eq_bot) n

@[simp]
theorem suzukiDF6D5B3ROddAmbientHilbertBasis_apply
    (n : SuzukiDF6D5B3RTailMode) :
    suzukiDF6D5B3ROddAmbientHilbertBasis n =
      suzukiDF6D5B3ROddAmbientMode n := by
  letI : CompleteSpace SuzukiDF6D5B3ROddAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TOddAmbientFarSubspace.completeSpace_coe
  exact congr_fun (HilbertBasis.coe_mkOfOrthogonalEqBot
    suzukiDF6D5B3ROddAmbientMode_orthonormal
    suzukiDF6D5B3ROddAmbientMode_orthogonal_eq_bot) n

/-! ## Actual residual representers and their coefficients -/

def suzukiDF6D5B3REEvenActualResidualRepresenter
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) : SuzukiDF6D5B3REvenAmbientFarL2 :=
  suzukiDF6D5B3REvenAmbientRepresenter
    (suzukiDF6D5B3REEvenAmbientResidualFunctional hsource i)

def suzukiDF6D5B3REOddActualResidualRepresenter
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) : SuzukiDF6D5B3ROddAmbientFarL2 :=
  suzukiDF6D5B3ROddAmbientRepresenter
    (suzukiDF6D5B3REOddAmbientResidualFunctional hsource i)

theorem suzukiDF6D5B3REEvenActualResidualRepresenter_coefficient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i : Fin 45) (n : SuzukiDF6D5B3RTailMode) :
    inner Complex (suzukiDF6D5B3REvenAmbientMode n)
        (suzukiDF6D5B3REEvenActualResidualRepresenter hsource i) =
      (suzukiDF6D5B3REvenFullResidualCoefficient i n : Complex) := by
  exact suzukiDF6D5B3REvenAmbientRepresenter_coefficient i _
    (suzukiDF6D5B3REEvenAmbientResidualFunctional_coefficient
      hsource hequation25 i) n

theorem suzukiDF6D5B3REOddActualResidualRepresenter_coefficient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i : Fin 44) (n : SuzukiDF6D5B3RTailMode) :
    inner Complex (suzukiDF6D5B3ROddAmbientMode n)
        (suzukiDF6D5B3REOddActualResidualRepresenter hsource i) =
      (suzukiDF6D5B3ROddFullResidualCoefficient i n : Complex) := by
  exact suzukiDF6D5B3ROddAmbientRepresenter_coefficient i _
    (suzukiDF6D5B3REOddAmbientResidualFunctional_coefficient
      hsource hequation25 i) n

/-! ## Quadratic Parseval receivers -/

theorem suzukiDF6D5B3REEvenActualResidualRepresenter_sum_coefficient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x : Fin 45 → Real) (n : SuzukiDF6D5B3RTailMode) :
    inner Complex (suzukiDF6D5B3REvenAmbientHilbertBasis n)
        (∑ i : Fin 45, (x i : Complex) •
          suzukiDF6D5B3REEvenActualResidualRepresenter hsource i) =
      ((∑ i : Fin 45,
        x i * suzukiDF6D5B3REvenFullResidualCoefficient i n : Real) :
          Complex) := by
  rw [suzukiDF6D5B3REvenAmbientHilbertBasis_apply, inner_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  calc
    inner Complex (suzukiDF6D5B3REvenAmbientMode n)
        ((x i : Complex) •
          suzukiDF6D5B3REEvenActualResidualRepresenter hsource i) =
        (x i : Complex) *
          inner Complex (suzukiDF6D5B3REvenAmbientMode n)
            (suzukiDF6D5B3REEvenActualResidualRepresenter hsource i) :=
      @inner_smul_right Complex SuzukiDF6D5B3REvenAmbientFarL2
        _ _ _ _ _ _
    _ = (x i : Complex) *
        (suzukiDF6D5B3REvenFullResidualCoefficient i n : Complex) := by
      rw [suzukiDF6D5B3REEvenActualResidualRepresenter_coefficient
        hsource hequation25]

theorem suzukiDF6D5B3REOddActualResidualRepresenter_sum_coefficient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x : Fin 44 → Real) (n : SuzukiDF6D5B3RTailMode) :
    inner Complex (suzukiDF6D5B3ROddAmbientHilbertBasis n)
        (∑ i : Fin 44, (x i : Complex) •
          suzukiDF6D5B3REOddActualResidualRepresenter hsource i) =
      ((∑ i : Fin 44,
        x i * suzukiDF6D5B3ROddFullResidualCoefficient i n : Real) :
          Complex) := by
  rw [suzukiDF6D5B3ROddAmbientHilbertBasis_apply, inner_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  calc
    inner Complex (suzukiDF6D5B3ROddAmbientMode n)
        ((x i : Complex) •
          suzukiDF6D5B3REOddActualResidualRepresenter hsource i) =
        (x i : Complex) *
          inner Complex (suzukiDF6D5B3ROddAmbientMode n)
            (suzukiDF6D5B3REOddActualResidualRepresenter hsource i) :=
      @inner_smul_right Complex SuzukiDF6D5B3ROddAmbientFarL2
        _ _ _ _ _ _
    _ = (x i : Complex) *
        (suzukiDF6D5B3ROddFullResidualCoefficient i n : Complex) := by
      rw [suzukiDF6D5B3REOddActualResidualRepresenter_coefficient
        hsource hequation25]

theorem suzukiDF6D5B3REEvenActualResidualRepresenter_parseval
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x : Fin 45 → Real) :
    ‖∑ i : Fin 45, (x i : Complex) •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i‖ ^ 2 =
      ∑' n : SuzukiDF6D5B3RTailMode,
        (∑ i : Fin 45,
          x i * suzukiDF6D5B3REvenFullResidualCoefficient i n) ^ 2 := by
  letI : CompleteSpace SuzukiDF6D5B3REvenAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace.completeSpace_coe
  let v := ∑ i : Fin 45, (x i : Complex) •
    suzukiDF6D5B3REEvenActualResidualRepresenter hsource i
  have hcoeff (n : SuzukiDF6D5B3RTailMode) :
      inner Complex (suzukiDF6D5B3REvenAmbientHilbertBasis n) v =
        ((∑ i : Fin 45,
          x i * suzukiDF6D5B3REvenFullResidualCoefficient i n : Real) :
            Complex) := by
    rw [show v = ∑ i : Fin 45, (x i : Complex) •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i by rfl,
      suzukiDF6D5B3REvenAmbientHilbertBasis_apply, inner_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    calc
      inner Complex (suzukiDF6D5B3REvenAmbientMode n)
          ((x i : Complex) •
            suzukiDF6D5B3REEvenActualResidualRepresenter hsource i) =
          (x i : Complex) *
            inner Complex (suzukiDF6D5B3REvenAmbientMode n)
              (suzukiDF6D5B3REEvenActualResidualRepresenter hsource i) :=
        @inner_smul_right Complex SuzukiDF6D5B3REvenAmbientFarL2
          _ _ _ _ _ _
      _ = (x i : Complex) *
          (suzukiDF6D5B3REvenFullResidualCoefficient i n : Complex) := by
        rw [suzukiDF6D5B3REEvenActualResidualRepresenter_coefficient
          hsource hequation25]
  have hparseval :=
    suzukiDF6D5B3REvenAmbientHilbertBasis.tsum_inner_mul_inner v v
  rw [inner_self_eq_norm_sq_to_K] at hparseval
  have hterm (n : SuzukiDF6D5B3RTailMode) :
      inner Complex v (suzukiDF6D5B3REvenAmbientHilbertBasis n) *
          inner Complex (suzukiDF6D5B3REvenAmbientHilbertBasis n) v =
        (((∑ i : Fin 45,
          x i * suzukiDF6D5B3REvenFullResidualCoefficient i n) ^ 2 :
            Real) : Complex) := by
    rw [← inner_conj_symm, hcoeff]
    simp
    ring
  rw [tsum_congr hterm] at hparseval
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, Complex.ofReal_pow]
  exact hparseval.symm

theorem suzukiDF6D5B3REOddActualResidualRepresenter_parseval
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x : Fin 44 → Real) :
    ‖∑ i : Fin 44, (x i : Complex) •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i‖ ^ 2 =
      ∑' n : SuzukiDF6D5B3RTailMode,
        (∑ i : Fin 44,
          x i * suzukiDF6D5B3ROddFullResidualCoefficient i n) ^ 2 := by
  letI : CompleteSpace SuzukiDF6D5B3ROddAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TOddAmbientFarSubspace.completeSpace_coe
  let v := ∑ i : Fin 44, (x i : Complex) •
    suzukiDF6D5B3REOddActualResidualRepresenter hsource i
  have hcoeff (n : SuzukiDF6D5B3RTailMode) :
      inner Complex (suzukiDF6D5B3ROddAmbientHilbertBasis n) v =
        ((∑ i : Fin 44,
          x i * suzukiDF6D5B3ROddFullResidualCoefficient i n : Real) :
            Complex) := by
    rw [show v = ∑ i : Fin 44, (x i : Complex) •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i by rfl,
      suzukiDF6D5B3ROddAmbientHilbertBasis_apply, inner_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    calc
      inner Complex (suzukiDF6D5B3ROddAmbientMode n)
          ((x i : Complex) •
            suzukiDF6D5B3REOddActualResidualRepresenter hsource i) =
          (x i : Complex) *
            inner Complex (suzukiDF6D5B3ROddAmbientMode n)
              (suzukiDF6D5B3REOddActualResidualRepresenter hsource i) :=
        @inner_smul_right Complex SuzukiDF6D5B3ROddAmbientFarL2
          _ _ _ _ _ _
      _ = (x i : Complex) *
          (suzukiDF6D5B3ROddFullResidualCoefficient i n : Complex) := by
        rw [suzukiDF6D5B3REOddActualResidualRepresenter_coefficient
          hsource hequation25]
  have hparseval :=
    suzukiDF6D5B3ROddAmbientHilbertBasis.tsum_inner_mul_inner v v
  rw [inner_self_eq_norm_sq_to_K] at hparseval
  have hterm (n : SuzukiDF6D5B3RTailMode) :
      inner Complex v (suzukiDF6D5B3ROddAmbientHilbertBasis n) *
          inner Complex (suzukiDF6D5B3ROddAmbientHilbertBasis n) v =
        (((∑ i : Fin 44,
          x i * suzukiDF6D5B3ROddFullResidualCoefficient i n) ^ 2 :
            Real) : Complex) := by
    rw [← inner_conj_symm, hcoeff]
    simp
    ring
  rw [tsum_congr hterm] at hparseval
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, Complex.ofReal_pow]
  exact hparseval.symm

end

end RiemannHypothesisProject.Experiments.M100
