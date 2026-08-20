import RiemannHypothesisProject.Experiments.M100.Polarization
import RiemannHypothesisProject.WeilPositivity.BurnolLocalSupport

/-!
# M100-X05 exact two-block positive-semidefinite criterion

This experimental module identifies the complete scalar criterion for a
two-block restriction of the checked Schwartz Weil form.  It also records the
support-closure consequence: positivity on one common support class already
controls every cross term between two members of that class.

No theorem below enlarges a Burnol support interval, proves translation
invariance of its spectral form, or supplies a criterion-determining class.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open SchwartzLineTestFunction

noncomputable section

/-- The real quadratic polynomial associated with a symmetric two-by-two
Gram matrix with diagonal entries `qg`, `qh` and cross entry `cross`. -/
def twoBlockQuadratic
    (qg qh cross a b : Real) : Real :=
  qg * a ^ 2 + 2 * cross * a * b + qh * b ^ 2

/-- The scalar Schur criterion is sufficient for two-block positivity. -/
theorem twoBlockQuadratic_nonnegative_of_schur
    {qg qh cross : Real}
    (hqg : 0 ≤ qg)
    (hqh : 0 ≤ qh)
    (hschur : cross ^ 2 ≤ qg * qh) :
    ∀ a b, 0 ≤ twoBlockQuadratic qg qh cross a b := by
  intro a b
  by_cases hqg_zero : qg = 0
  · have hcross : cross = 0 := by
      subst qg
      simp only [zero_mul] at hschur
      nlinarith [sq_nonneg cross]
    subst qg
    subst cross
    unfold twoBlockQuadratic
    nlinarith [mul_nonneg hqh (sq_nonneg b)]
  · have hqg_pos : 0 < qg := lt_of_le_of_ne hqg (Ne.symm hqg_zero)
    have hidentity :
        qg * twoBlockQuadratic qg qh cross a b =
          (qg * a + cross * b) ^ 2 +
            (qg * qh - cross ^ 2) * b ^ 2 := by
      unfold twoBlockQuadratic
      ring
    have hright :
        0 ≤ (qg * a + cross * b) ^ 2 +
          (qg * qh - cross ^ 2) * b ^ 2 :=
      add_nonneg (sq_nonneg _)
        (mul_nonneg (sub_nonneg.mpr hschur) (sq_nonneg b))
    have hproduct : 0 ≤ qg * twoBlockQuadratic qg qh cross a b := by
      rw [hidentity]
      exact hright
    apply nonneg_of_mul_nonneg_left ?_ hqg_pos
    simpa [mul_comm] using hproduct

/-- Positivity of every real two-block combination forces the diagonal and
Schur conditions. -/
theorem schur_of_twoBlockQuadratic_nonnegative
    {qg qh cross : Real}
    (hall : ∀ a b, 0 ≤ twoBlockQuadratic qg qh cross a b) :
    0 ≤ qg ∧ 0 ≤ qh ∧ cross ^ 2 ≤ qg * qh := by
  have hqg : 0 ≤ qg := by
    simpa [twoBlockQuadratic] using hall 1 0
  have hqh : 0 ≤ qh := by
    simpa [twoBlockQuadratic] using hall 0 1
  refine ⟨hqg, hqh, ?_⟩
  by_cases hqg_zero : qg = 0
  · subst qg
    by_cases hqh_zero : qh = 0
    · subst qh
      have htest := hall 1 (-cross)
      simp only [twoBlockQuadratic, zero_mul, zero_add] at htest
      nlinarith [sq_nonneg cross]
    · have hqh_pos : 0 < qh := lt_of_le_of_ne hqh (Ne.symm hqh_zero)
      have htest := hall qh (-cross)
      simp only [twoBlockQuadratic, zero_mul, zero_add] at htest
      nlinarith [sq_nonneg cross]
  · have hqg_pos : 0 < qg := lt_of_le_of_ne hqg (Ne.symm hqg_zero)
    have htest := hall (-cross) qg
    unfold twoBlockQuadratic at htest
    nlinarith [sq_nonneg cross, sq_nonneg qg]

/-- Exact scalar characterization of a positive-semidefinite two-by-two Gram
matrix. -/
theorem twoBlockQuadratic_nonnegative_iff_schur
    {qg qh cross : Real} :
    (∀ a b, 0 ≤ twoBlockQuadratic qg qh cross a b) ↔
      0 ≤ qg ∧ 0 ≤ qh ∧ cross ^ 2 ≤ qg * qh := by
  constructor
  · exact schur_of_twoBlockQuadratic_nonnegative
  · rintro ⟨hqg, hqh, hschur⟩
    exact twoBlockQuadratic_nonnegative_of_schur hqg hqh hschur

theorem schwartzCrossCorrelation_real_smul_left
    (r : Real) (g h : SchwartzLineTestFunction) :
    schwartzCrossCorrelation (r • g) h =
      r • schwartzCrossCorrelation g h := by
  change schwartzCrossCorrelation ((r : Complex) • g) h =
    (r : Complex) • schwartzCrossCorrelation g h
  simp [schwartzCrossCorrelation]

theorem schwartzCrossCorrelation_real_smul_right
    (r : Real) (g h : SchwartzLineTestFunction) :
    schwartzCrossCorrelation g (r • h) =
      r • schwartzCrossCorrelation g h := by
  change schwartzCrossCorrelation g ((r : Complex) • h) =
    (r : Complex) • schwartzCrossCorrelation g h
  simp [schwartzCrossCorrelation]

/-- Real linearity of the checked polarized form in its first input. -/
theorem schwartzWeilPolarizedForm_real_smul_left
    (data : SchwartzWeilQuadraticFormData)
    (r : Real) (g h : SchwartzLineTestFunction) :
    schwartzWeilPolarizedForm data (r • g) h =
      r * schwartzWeilPolarizedForm data g h := by
  simp only [schwartzWeilPolarizedForm,
    schwartzCrossCorrelation_real_smul_left,
    schwartzCrossCorrelation_real_smul_right, ← smul_add, map_smul]
  ring

/-- Real linearity of the checked polarized form in its second input. -/
theorem schwartzWeilPolarizedForm_real_smul_right
    (data : SchwartzWeilQuadraticFormData)
    (r : Real) (g h : SchwartzLineTestFunction) :
    schwartzWeilPolarizedForm data g (r • h) =
      r * schwartzWeilPolarizedForm data g h := by
  rw [schwartzWeilPolarizedForm_symm,
    schwartzWeilPolarizedForm_real_smul_left,
    schwartzWeilPolarizedForm_symm]

/-- Exact quadratic polynomial for a real linear combination of two checked
base tests. -/
theorem quadraticForm_twoBlock_real_smul
    (data : SchwartzWeilQuadraticFormData)
    (a b : Real) (g h : SchwartzLineTestFunction) :
    data.quadraticForm (a • g + b • h) =
      twoBlockQuadratic (data.quadraticForm g) (data.quadraticForm h)
        (schwartzWeilPolarizedForm data g h) a b := by
  rw [quadraticForm_add_eq_polarized,
    SchwartzWeilQuadraticFormData.quadraticForm_smul,
    SchwartzWeilQuadraticFormData.quadraticForm_smul,
    schwartzWeilPolarizedForm_real_smul_left,
    schwartzWeilPolarizedForm_real_smul_right]
  unfold twoBlockQuadratic
  ring

/-- Exact two-block PSD criterion for the checked Schwartz Weil form. -/
theorem quadraticForm_twoBlock_nonnegative_iff_schur
    (data : SchwartzWeilQuadraticFormData)
    (g h : SchwartzLineTestFunction) :
    (∀ a b : Real, 0 ≤ data.quadraticForm (a • g + b • h)) ↔
      0 ≤ data.quadraticForm g ∧
      0 ≤ data.quadraticForm h ∧
      schwartzWeilPolarizedForm data g h ^ 2 ≤
        data.quadraticForm g * data.quadraticForm h := by
  simpa only [quadraticForm_twoBlock_real_smul] using
    (twoBlockQuadratic_nonnegative_iff_schur
      (qg := data.quadraticForm g)
      (qh := data.quadraticForm h)
      (cross := schwartzWeilPolarizedForm data g h))

/-- A common pointwise support class is closed under real two-block linear
combinations. -/
theorem support_twoBlock_real_smul_subset
    {S : Set Real}
    {g h : SchwartzLineTestFunction}
    (hg : Function.support g ⊆ S)
    (hh : Function.support h ⊆ S)
    (a b : Real) :
    Function.support (a • g + b • h) ⊆ S := by
  intro x hx
  by_contra hxS
  have hg_zero : g x = 0 := by
    by_contra hg_nonzero
    exact hxS (hg hg_nonzero)
  have hh_zero : h x = 0 := by
    by_contra hh_nonzero
    exact hxS (hh hh_nonzero)
  apply hx
  simp [hg_zero, hh_zero]

/-- Positivity on one common support class already implies the complete Schur
bound for every pair in that class.  This does not enlarge the class. -/
theorem polarized_schur_of_common_support_nonnegative
    (data : SchwartzWeilQuadraticFormData)
    {S : Set Real}
    (hnonnegative : ∀ f : SchwartzLineTestFunction,
      Function.support f ⊆ S → 0 ≤ data.quadraticForm f)
    {g h : SchwartzLineTestFunction}
    (hg : Function.support g ⊆ S)
    (hh : Function.support h ⊆ S) :
    schwartzWeilPolarizedForm data g h ^ 2 ≤
      data.quadraticForm g * data.quadraticForm h := by
  have hall : ∀ a b : Real,
      0 ≤ data.quadraticForm (a • g + b • h) := by
    intro a b
    exact hnonnegative _ (support_twoBlock_real_smul_subset hg hh a b)
  exact (quadraticForm_twoBlock_nonnegative_iff_schur data g h).mp hall |>.2.2

/-- The production Burnol fixed-support theorem already controls every real
combination of two blocks in its one common centered interval.  The Binet
source theorem remains an explicit hypothesis, and the interval is still only
existentially supplied. -/
theorem exists_burnolFixedSupport_twoBlock_nonneg_of_binet
    (hBinet : ComplexCompactExhaustion.BennettGammaBinetDigammaFormula) :
    ∃ epsilon > 0,
      ∀ g h : SchwartzLineTestFunction,
        Function.support g ⊆
            Set.Icc (-(epsilon / (8 * Real.pi)))
              (epsilon / (8 * Real.pi)) →
        Function.support h ⊆
            Set.Icc (-(epsilon / (8 * Real.pi)))
              (epsilon / (8 * Real.pi)) →
        ∀ a b : Real,
          0 ≤ burnolLocalSpectralQuadraticForm (a • g + b • h) := by
  obtain ⟨epsilon, hepsilon, A, hA, hfixed⟩ :=
    exists_burnolFixedSupport_spectral_nonneg_of_binet hBinet
  refine ⟨epsilon, hepsilon, ?_⟩
  intro g h hg hh a b
  exact hfixed _ (support_twoBlock_real_smul_subset hg hh a b)

end

end M100
end Experiments
end RiemannHypothesisProject
