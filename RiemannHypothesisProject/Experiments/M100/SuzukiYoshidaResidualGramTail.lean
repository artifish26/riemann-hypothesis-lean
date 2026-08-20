import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaResidualParseval
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly

/-!
# Finite Gram and analytic tail for the B3R-E residual representers

This module splits the physical residual Parseval sum at the frozen DF6D4
cutoffs and consumes the existing finite-Gram and `601+` analytic-tail bounds.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The exact three-way decomposition of physical modes `n ≥ 45` used by the
frozen residual certificate. -/
def suzukiDF6D5B3RResidualModeSplitEquiv :
    Fin 256 ⊕ (Fin 300 ⊕ Nat) ≃ SuzukiDF6D5B3RTailMode where
  toFun
    | Sum.inl j => ⟨45 + j.1, by omega⟩
    | Sum.inr (Sum.inl r) => ⟨301 + r.1, by omega⟩
    | Sum.inr (Sum.inr k) => ⟨601 + k, by omega⟩
  invFun n :=
    if h₁ : n.1 < 301 then
      Sum.inl ⟨n.1 - 45, by omega⟩
    else if h₂ : n.1 < 601 then
      Sum.inr (Sum.inl ⟨n.1 - 301, by omega⟩)
    else
      Sum.inr (Sum.inr (n.1 - 601))
  left_inv s := by
    rcases s with j | r
    · have h : 45 + j.1 < 301 := by omega
      simp [h]
    · rcases r with r | k
      · have h₁ : ¬ 301 + r.1 < 301 := by omega
        have h₂ : 301 + r.1 < 601 := by omega
        simp [h₁, h₂]
      · have h₁ : ¬ 601 + k < 301 := by omega
        have h₂ : ¬ 601 + k < 601 := by omega
        simp [h₁, h₂]
  right_inv n := by
    by_cases h₁ : n.1 < 301
    · simp only [h₁, dif_pos]
      apply Subtype.ext
      change 45 + (n.1 - 45) = n.1
      omega
    · by_cases h₂ : n.1 < 601
      · simp only [h₁, h₂, dif_pos]
        apply Subtype.ext
        change 301 + (n.1 - 301) = n.1
        omega
      · simp only [h₁, h₂]
        apply Subtype.ext
        change 601 + (n.1 - 601) = n.1
        omega

private theorem finite_residual_gram_quadratic
    {rows columns : Nat}
    (R : Fin rows → Fin columns → Real)
    (x : Fin columns → Real) :
    (∑ k : Fin rows, (∑ i : Fin columns, x i * R k i) ^ 2) =
      ∑ i : Fin columns, x i *
        ∑ j : Fin columns, (∑ k : Fin rows, R k i * R k j) * x j := by
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem suzukiDF6D5B3REvenFiniteResidualQuadratic_eq
    (x : Fin 45 → Real) :
    (∑ k : Fin 256,
        (∑ i : Fin 45,
          x i * suzukiDF6D4EvenGalerkinSolveResidual k i) ^ 2) +
      (∑ r : Fin 300,
        (∑ i : Fin 45,
          x i * suzukiDF6D4EvenResidualColumn (301 + r.1) i) ^ 2) =
      dotProduct x
        (Matrix.mulVec suzukiDF6D4EvenFiniteResidualGramMatrix x) := by
  rw [finite_residual_gram_quadratic, finite_residual_gram_quadratic]
  unfold dotProduct Matrix.mulVec
    suzukiDF6D4EvenFiniteResidualGramMatrix
    suzukiDF6D4EvenFiniteResidualGramEntry
  simp only [dotProduct]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem suzukiDF6D5B3ROddFiniteResidualQuadratic_eq
    (x : Fin 44 → Real) :
    (∑ k : Fin 256,
        (∑ i : Fin 44,
          x i * suzukiDF6D4OddGalerkinSolveResidual k i) ^ 2) +
      (∑ r : Fin 300,
        (∑ i : Fin 44,
          x i * suzukiDF6D4OddResidualColumn (301 + r.1) i) ^ 2) =
      dotProduct x
        (Matrix.mulVec suzukiDF6D4OddFiniteResidualGramMatrix x) := by
  rw [finite_residual_gram_quadratic, finite_residual_gram_quadratic]
  unfold dotProduct Matrix.mulVec
    suzukiDF6D4OddFiniteResidualGramMatrix
    suzukiDF6D4OddFiniteResidualGramEntry
  simp only [dotProduct]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem residual_square_tsum_split
    (coefficient : SuzukiDF6D5B3RTailMode → Real)
    (hsum : Summable fun n => (coefficient n) ^ 2) :
    (∑' n : SuzukiDF6D5B3RTailMode, (coefficient n) ^ 2) =
      (∑ j : Fin 256, (coefficient
        ⟨45 + j.1, by omega⟩) ^ 2) +
      (∑ r : Fin 300, (coefficient
        ⟨301 + r.1, by omega⟩) ^ 2) +
      ∑' k : Nat, (coefficient ⟨601 + k, by omega⟩) ^ 2 := by
  rw [← suzukiDF6D5B3RResidualModeSplitEquiv.tsum_eq]
  have hs : Summable fun c : Fin 256 ⊕ (Fin 300 ⊕ Nat) =>
      (coefficient (suzukiDF6D5B3RResidualModeSplitEquiv c)) ^ 2 :=
    suzukiDF6D5B3RResidualModeSplitEquiv.summable_iff.mpr hsum
  have hsLeft := hs.comp_injective Sum.inl_injective
  have hsRight := hs.comp_injective Sum.inr_injective
  have hsplit := hsLeft.tsum_sum hsRight
  rw [hsplit]
  have hsMiddle := hsRight.comp_injective Sum.inl_injective
  have hsTail := hsRight.comp_injective Sum.inr_injective
  have hright := hsMiddle.tsum_sum hsTail
  have hright' :
      (∑' i : Fin 300 ⊕ Nat,
        (coefficient
          (suzukiDF6D5B3RResidualModeSplitEquiv (Sum.inr i))) ^ 2) =
        (∑' r : Fin 300,
          (coefficient
            (suzukiDF6D5B3RResidualModeSplitEquiv
              (Sum.inr (Sum.inl r)))) ^ 2) +
        ∑' k : Nat,
          (coefficient
            (suzukiDF6D5B3RResidualModeSplitEquiv
              (Sum.inr (Sum.inr k)))) ^ 2 := by
    simpa only [Function.comp_apply] using hright
  rw [hright', tsum_fintype, tsum_fintype]
  simp [suzukiDF6D5B3RResidualModeSplitEquiv, add_assoc]

private theorem suzukiDF6D5B3REvenResidualSquare_summable
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x : Fin 45 → Real) :
    Summable fun n : SuzukiDF6D5B3RTailMode =>
      (∑ i : Fin 45,
        x i * suzukiDF6D5B3REvenFullResidualCoefficient i n) ^ 2 := by
  letI : CompleteSpace SuzukiDF6D5B3REvenAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace.completeSpace_coe
  let v := ∑ i : Fin 45, (x i : Complex) •
    suzukiDF6D5B3REEvenActualResidualRepresenter hsource i
  have hb :=
    suzukiDF6D5B3REvenAmbientHilbertBasis.summable_inner_mul_inner v v
  have hc : Summable fun n : SuzukiDF6D5B3RTailMode =>
      (((∑ i : Fin 45,
        x i * suzukiDF6D5B3REvenFullResidualCoefficient i n) ^ 2 : Real) :
          Complex) := by
    apply hb.congr
    intro n
    rw [← inner_conj_symm,
      suzukiDF6D5B3REEvenActualResidualRepresenter_sum_coefficient
        hsource hequation25 x]
    simp
    ring
  exact Complex.summable_ofReal.mp hc

private theorem suzukiDF6D5B3ROddResidualSquare_summable
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x : Fin 44 → Real) :
    Summable fun n : SuzukiDF6D5B3RTailMode =>
      (∑ i : Fin 44,
        x i * suzukiDF6D5B3ROddFullResidualCoefficient i n) ^ 2 := by
  letI : CompleteSpace SuzukiDF6D5B3ROddAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TOddAmbientFarSubspace.completeSpace_coe
  let v := ∑ i : Fin 44, (x i : Complex) •
    suzukiDF6D5B3REOddActualResidualRepresenter hsource i
  have hb :=
    suzukiDF6D5B3ROddAmbientHilbertBasis.summable_inner_mul_inner v v
  have hc : Summable fun n : SuzukiDF6D5B3RTailMode =>
      (((∑ i : Fin 44,
        x i * suzukiDF6D5B3ROddFullResidualCoefficient i n) ^ 2 : Real) :
          Complex) := by
    apply hb.congr
    intro n
    rw [← inner_conj_symm,
      suzukiDF6D5B3REOddActualResidualRepresenter_sum_coefficient
        hsource hequation25 x]
    simp
    ring
  exact Complex.summable_ofReal.mp hc

theorem suzukiDF6D5B3REEvenActualResidualRepresenter_norm_sq_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x : Fin 45 → Real) :
    ‖∑ i : Fin 45, (x i : Complex) •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i‖ ^ 2 ≤
      dotProduct x
          (Matrix.mulVec suzukiDF6D4EvenFiniteResidualGramMatrix x) +
        dotProduct x
          (Matrix.mulVec suzukiDF6D4EvenAnalyticTailMatrix x) := by
  rw [suzukiDF6D5B3REEvenActualResidualRepresenter_parseval
    hsource hequation25]
  rw [residual_square_tsum_split _
    (suzukiDF6D5B3REvenResidualSquare_summable hsource hequation25 x)]
  have hgal (j : Fin 256) (i : Fin 45) :
      suzukiDF6D5B3REvenFullResidualCoefficient i
          ⟨45 + j.1, by omega⟩ =
        suzukiDF6D4EvenGalerkinSolveResidual j i := by
    simpa [suzukiDF6D4GalerkinMode] using
      suzukiDF6D5B3REvenFullResidualCoefficient_galerkin i j
  have hcol (mode : Nat) (hmode : 301 ≤ mode) (i : Fin 45) :
      suzukiDF6D5B3REvenFullResidualCoefficient i
          ⟨mode, by omega⟩ =
        suzukiDF6D4EvenResidualColumn mode i :=
    suzukiDF6D5B3REvenFullResidualCoefficient_of_ge i mode hmode
  have hcolFinite (r : Fin 300) (i : Fin 45) :
      suzukiDF6D5B3REvenFullResidualCoefficient i
          ⟨301 + r.1, by omega⟩ =
        suzukiDF6D4EvenResidualColumn (301 + r.1) i :=
    hcol (301 + r.1) (by omega) i
  have hcolTail (k : Nat) (i : Fin 45) :
      suzukiDF6D5B3REvenFullResidualCoefficient i
          ⟨601 + k, by omega⟩ =
        suzukiDF6D4EvenResidualColumn (601 + k) i :=
    hcol (601 + k) (by omega) i
  simp_rw [hgal, hcolFinite, hcolTail]
  rw [suzukiDF6D5B3REvenFiniteResidualQuadratic_eq]
  exact add_le_add_right
    (suzukiDF6D4EvenResidualTailQuadratic_le_analyticMatrix x) _

theorem suzukiDF6D5B3REOddActualResidualRepresenter_norm_sq_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x : Fin 44 → Real) :
    ‖∑ i : Fin 44, (x i : Complex) •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i‖ ^ 2 ≤
      dotProduct x
          (Matrix.mulVec suzukiDF6D4OddFiniteResidualGramMatrix x) +
        dotProduct x
          (Matrix.mulVec suzukiDF6D4OddAnalyticTailMatrix x) := by
  rw [suzukiDF6D5B3REOddActualResidualRepresenter_parseval
    hsource hequation25]
  rw [residual_square_tsum_split _
    (suzukiDF6D5B3ROddResidualSquare_summable hsource hequation25 x)]
  have hgal (j : Fin 256) (i : Fin 44) :
      suzukiDF6D5B3ROddFullResidualCoefficient i
          ⟨45 + j.1, by omega⟩ =
        suzukiDF6D4OddGalerkinSolveResidual j i := by
    simpa [suzukiDF6D4GalerkinMode] using
      suzukiDF6D5B3ROddFullResidualCoefficient_galerkin i j
  have hcol (mode : Nat) (hmode : 301 ≤ mode) (i : Fin 44) :
      suzukiDF6D5B3ROddFullResidualCoefficient i
          ⟨mode, by omega⟩ =
        suzukiDF6D4OddResidualColumn mode i :=
    suzukiDF6D5B3ROddFullResidualCoefficient_of_ge i mode hmode
  have hcolFinite (r : Fin 300) (i : Fin 44) :
      suzukiDF6D5B3ROddFullResidualCoefficient i
          ⟨301 + r.1, by omega⟩ =
        suzukiDF6D4OddResidualColumn (301 + r.1) i :=
    hcol (301 + r.1) (by omega) i
  have hcolTail (k : Nat) (i : Fin 44) :
      suzukiDF6D5B3ROddFullResidualCoefficient i
          ⟨601 + k, by omega⟩ =
        suzukiDF6D4OddResidualColumn (601 + k) i :=
    hcol (601 + k) (by omega) i
  simp_rw [hgal, hcolFinite, hcolTail]
  rw [suzukiDF6D5B3ROddFiniteResidualQuadratic_eq]
  exact add_le_add_right
    (suzukiDF6D4OddResidualTailQuadratic_le_analyticMatrix x) _

end

end RiemannHypothesisProject.Experiments.M100
