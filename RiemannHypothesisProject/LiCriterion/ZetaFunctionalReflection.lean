import RiemannHypothesisProject.LiCriterion.ZetaLiCoefficient

/-!
# Functional reflection of nontrivial zeta zeros

The completed-zeta functional equation reflects a nontrivial zero `rho` to
`1 - rho`.  This module keeps the reflection bridge in the Li-criterion layer
and proves every cleanup condition explicitly: neither endpoint is zero or
one, the completed value vanishes, and the reflected zero is nontrivial.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- A zeta zero cannot be zero. -/
theorem isZetaZero_ne_zero {rho : Complex} (hrho : IsZetaZero rho) :
    rho ≠ 0 := by
  intro hrho_zero
  rw [hrho_zero] at hrho
  norm_num [IsZetaZero, riemannZeta_zero] at hrho

/-- The completed zeta function vanishes at every nontrivial zeta zero. -/
theorem completedRiemannZeta_eq_zero_of_isNontrivialZetaZero
    {rho : Complex} (hrho : IsNontrivialZetaZero rho) :
    completedRiemannZeta rho = 0 := by
  have hrho_zero : rho ≠ 0 := isZetaZero_ne_zero hrho.1
  have hrho_im_ne : rho.im ≠ 0 :=
    isNontrivialZetaZero_im_ne_zero ⟨rho, hrho.1⟩ hrho.2.1
  have hgamma : Complex.Gammaℝ rho ≠ 0 := by
    intro hgamma_zero
    rcases Complex.Gammaℝ_eq_zero_iff.mp hgamma_zero with ⟨n, hn⟩
    apply hrho_im_ne
    rw [hn]
    simp
  have hzeta : riemannZeta rho = 0 := hrho.1
  rw [riemannZeta_def_of_ne_zero hrho_zero] at hzeta
  exact (div_eq_zero_iff.mp hzeta).resolve_right hgamma

/-- The functional reflection `rho ↦ 1 - rho` preserves nontrivial zeta
zeros. -/
theorem isNontrivialZetaZero_one_sub
    {rho : Complex} (hrho : IsNontrivialZetaZero rho) :
    IsNontrivialZetaZero (1 - rho) := by
  have hrho_zero : rho ≠ 0 := isZetaZero_ne_zero hrho.1
  have hmirror_zero : 1 - rho ≠ 0 :=
    sub_ne_zero.mpr hrho.2.2.symm
  have hcompleted : completedRiemannZeta rho = 0 :=
    completedRiemannZeta_eq_zero_of_isNontrivialZetaZero hrho
  have hmirror_completed : completedRiemannZeta (1 - rho) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hcompleted
  have hmirror_zeta : IsZetaZero (1 - rho) := by
    unfold IsZetaZero
    rw [riemannZeta_def_of_ne_zero hmirror_zero, hmirror_completed, zero_div]
  have hrho_im_ne : rho.im ≠ 0 :=
    isNontrivialZetaZero_im_ne_zero ⟨rho, hrho.1⟩ hrho.2.1
  have hmirror_not_trivial : ¬ IsTrivialZetaZero (1 - rho) := by
    apply not_isTrivialZetaZero_of_im_ne_zero
    simpa using neg_ne_zero.mpr hrho_im_ne
  have hmirror_ne_one : 1 - rho ≠ 1 := by
    intro hmirror
    apply hrho_zero
    calc
      rho = 1 - (1 - rho) := by ring
      _ = 1 - 1 := by rw [hmirror]
      _ = 0 := by ring
  exact ⟨hmirror_zeta, hmirror_not_trivial, hmirror_ne_one⟩

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
