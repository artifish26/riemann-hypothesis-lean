import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Good-height selection

The elementary measure argument here selects a point in a unit interval that
stays quantitatively separated from a prescribed finite set of ordinates.
-/

namespace RiemannHypothesisProject

open MeasureTheory Metric Set

/-- A finite set of real ordinates leaves a point of every unit interval at
distance at least `1 / (4(card + 1))` from every ordinate. -/
theorem exists_mem_Icc_dist_finset_ge
    (s : Finset Real) (a : Real) :
    ∃ T ∈ Icc a (a + 1), ∀ y ∈ s,
      1 / (4 * ((s.card : Real) + 1)) <= dist T y := by
  let d : Real := 1 / (4 * ((s.card : Real) + 1))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  by_contra h
  push Not at h
  have hcover : Icc a (a + 1) ⊆ ⋃ y ∈ s, ball y d := by
    intro T hT
    obtain ⟨y, hy, hTy⟩ := h T hT
    exact mem_iUnion₂.mpr ⟨y, hy, hTy⟩
  have hmeasure :
      volume (Icc a (a + 1)) <= volume (⋃ y ∈ s, ball y d) :=
    measure_mono hcover
  have hunion :
      volume (⋃ y ∈ s, ball y d) <=
        ∑ y ∈ s, volume (ball y d) :=
    measure_biUnion_finset_le s (fun y => ball y d)
  have hsmall :
      (∑ y ∈ s, volume (ball y d)) < volume (Icc a (a + 1)) := by
    rw [Real.volume_Icc]
    simp only [add_sub_cancel_left, ENNReal.ofReal_one]
    rw [show (∑ y ∈ s, volume (ball y d)) =
        (s.card : ENNReal) * ENNReal.ofReal (2 * d) by
      simp [Real.volume_ball]]
    rw [← ENNReal.ofReal_natCast s.card,
      ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_one]
    dsimp [d]
    have hn : (0 : Real) <= s.card := by positivity
    have hden : 0 < 4 * ((s.card : Real) + 1) := by positivity
    rw [show (s.card : Real) *
          (2 * (1 / (4 * ((s.card : Real) + 1)))) =
        (2 * (s.card : Real)) / (4 * ((s.card : Real) + 1)) by
      field_simp]
    exact (div_lt_one hden).mpr (by linarith)
  exact (not_lt_of_ge (hmeasure.trans hunion)) hsmall

end RiemannHypothesisProject
