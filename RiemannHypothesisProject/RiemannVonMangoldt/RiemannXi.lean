import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RiemannHypothesisProject.RiemannVonMangoldt.CanonicalMultiplicityCount

/-!
# The entire Riemann xi function in Mathlib's completed-zeta normalization

Mathlib's `completedRiemannZeta₀` is the entire pole-subtracted completed zeta.
Multiplying its relation to `completedRiemannZeta` by `s * (s - 1)` gives the
classical xi normalization without division at `0` or `1`.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Riemann's entire xi function, normalized as
`(s * (s - 1) * Λ₀(s) + 1) / 2`. -/
def riemannXi (s : Complex) : Complex :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- The xi normalization is entire. -/
theorem differentiable_riemannXi : Differentiable Complex riemannXi := by
  unfold riemannXi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).div_const 2

/-- Xi is analytic on every set, in particular on every Jensen ball. -/
theorem analyticOnNhd_riemannXi (S : Set Complex) :
    AnalyticOnNhd Complex riemannXi S := by
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr
    differentiable_riemannXi).mono
    (Set.subset_univ S)

/-- Away from the removable points, xi is the classical polynomial multiple
of the meromorphic completed zeta. -/
theorem riemannXi_eq_completedRiemannZeta
    {s : Complex} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [completedRiemannZeta_eq]
  unfold riemannXi
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, hs1, h1s]
  ring

/-- Xi inherits the completed-zeta reflection symmetry. -/
theorem riemannXi_one_sub (s : Complex) :
    riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- The completed zeta is nonzero at the convenient Jensen center `2`. -/
theorem completedRiemannZeta_two_ne_zero :
    completedRiemannZeta 2 ≠ 0 := by
  have hzeta : riemannZeta (2 : Complex) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have heq :
      riemannZeta (2 : Complex) =
        completedRiemannZeta 2 / Complex.Gammaℝ 2 := by
    exact HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne
      (a := 0) (s := (2 : Complex)) (Or.inr (by norm_num))
  intro hzero
  apply hzeta
  rw [heq, hzero, zero_div]

/-- Xi is nonzero at the center `2`, as required by Jensen's inequality. -/
theorem riemannXi_two_ne_zero : riemannXi 2 ≠ 0 := by
  rw [riemannXi_eq_completedRiemannZeta (by norm_num) (by norm_num)]
  norm_num
  exact completedRiemannZeta_two_ne_zero

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
