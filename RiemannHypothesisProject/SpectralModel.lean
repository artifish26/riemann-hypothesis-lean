import RiemannHypothesisProject.ZetaSetup
import Mathlib.Data.Fintype.Basic

/-!
# Abstract spectral model

This is a deliberately small Hilbert-Polya-style interface. It does not assert
that such a model exists. It records the exact shape of result a spectral
construction would need: every nontrivial zero is realized by spectral data
whose image is already known to lie on the critical line.
-/

namespace RiemannHypothesisProject

/-- The point `1 / 2 + i * t` on the critical line. -/
noncomputable def criticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * Complex.I

theorem criticalLinePoint_on_line (t : ℝ) :
    IsCriticalLine (criticalLinePoint t) := by
  unfold IsCriticalLine criticalLinePoint
  simp

/--
A height realization of nontrivial zeta zeroes.

This is the most direct checked version of the Hilbert-Polya target: each zero
has a real spectral height `t`, and the zero itself is `1 / 2 + i * t`.
-/
structure HeightRealization where
  height : ∀ s : ℂ, IsNontrivialZetaZero s → ℝ
  realizes_nontrivial_zeroes :
    ∀ (s : ℂ) (hs : IsNontrivialZetaZero s), criticalLinePoint (height s hs) = s

/-- Any real-height realization of all nontrivial zeroes implies RH. -/
theorem RHStatement.of_heightRealization
    (model : HeightRealization) : RHStatement := by
  intro s hs
  rw [← model.realizes_nontrivial_zeroes s hs]
  exact criticalLinePoint_on_line (model.height s hs)

/-- Any real-height realization of all nontrivial zeroes implies Mathlib's RH. -/
theorem mathlib_RH_of_heightRealization
    (model : HeightRealization) : RiemannHypothesis := by
  exact RHStatement_iff_mathlib.mp (RHStatement.of_heightRealization model)

/-- RH restricted to a specified family of complex numbers. -/
def RHOn (family : ℂ → Prop) : Prop :=
  ∀ s : ℂ, family s → IsNontrivialZetaZero s → IsCriticalLine s

/--
A local real-height realization for a selected family of zeroes.

This is useful for finite windows or toy models: every nontrivial zero in the
family is represented as `1 / 2 + i * t` for some real height `t`.
-/
structure LocalHeightRealization (family : ℂ → Prop) where
  height : ∀ s : ℂ, family s → IsNontrivialZetaZero s → ℝ
  realizes_family_zeroes :
    ∀ (s : ℂ) (hs_family : family s) (hs_zero : IsNontrivialZetaZero s),
      criticalLinePoint (height s hs_family hs_zero) = s

/-- A local real-height realization proves RH on that family. -/
theorem RHOn.of_localHeightRealization {family : ℂ → Prop}
    (model : LocalHeightRealization family) : RHOn family := by
  intro s hs_family hs_zero
  rw [← model.realizes_family_zeroes s hs_family hs_zero]
  exact criticalLinePoint_on_line (model.height s hs_family hs_zero)

/--
A spectral realization of the nontrivial zeta zeroes whose spectral points all
land on the critical line.
-/
structure CriticalLineRealization where
  Carrier : Type
  spectralPoint : Carrier → ℂ
  spectralPoint_on_line : ∀ x : Carrier, IsCriticalLine (spectralPoint x)
  realizes_nontrivial_zeroes :
    ∀ s : ℂ, IsNontrivialZetaZero s → ∃ x : Carrier, spectralPoint x = s

/--
Any genuine critical-line spectral realization of all nontrivial zeroes implies
the Riemann Hypothesis.
-/
theorem RHStatement.of_criticalLineRealization
    (model : CriticalLineRealization) : RHStatement := by
  intro s hs
  rcases model.realizes_nontrivial_zeroes s hs with ⟨x, hx⟩
  rw [← hx]
  exact model.spectralPoint_on_line x

theorem mathlib_RH_of_criticalLineRealization
    (model : CriticalLineRealization) : RiemannHypothesis := by
  exact RHStatement_iff_mathlib.mp (RHStatement.of_criticalLineRealization model)

/--
A real-spectrum model whose spectral values are real heights.

This is closer to the Hilbert-Polya slogan: if a self-adjoint operator supplied
these real heights as spectral data, then the associated zeta zeroes would be on
the critical line.
-/
structure RealSpectrumModel where
  Carrier : Type
  height : Carrier → ℝ
  realizes_nontrivial_zeroes :
    ∀ s : ℂ, IsNontrivialZetaZero s → ∃ x : Carrier, criticalLinePoint (height x) = s

/-- A real-spectrum model gives a critical-line realization. -/
noncomputable def RealSpectrumModel.toCriticalLineRealization
    (model : RealSpectrumModel) : CriticalLineRealization where
  Carrier := model.Carrier
  spectralPoint x := criticalLinePoint (model.height x)
  spectralPoint_on_line x := criticalLinePoint_on_line (model.height x)
  realizes_nontrivial_zeroes := model.realizes_nontrivial_zeroes

/-- Any real-spectrum model realizing all nontrivial zeroes implies RH. -/
theorem RHStatement.of_realSpectrumModel
    (model : RealSpectrumModel) : RHStatement :=
  RHStatement.of_criticalLineRealization model.toCriticalLineRealization

/-- Any real-spectrum model realizing all nontrivial zeroes implies Mathlib's RH. -/
theorem mathlib_RH_of_realSpectrumModel
    (model : RealSpectrumModel) : RiemannHypothesis := by
  exact RHStatement_iff_mathlib.mp (RHStatement.of_realSpectrumModel model)

/--
A local real-spectrum model for a selected family of zeroes.

Unlike `RealSpectrumModel`, this only tries to realize nontrivial zeroes in a
chosen family. That makes it suitable for finite windows and toy examples.
-/
structure LocalRealSpectrumModel (family : ℂ → Prop) where
  Carrier : Type
  height : Carrier → ℝ
  realizes_family_zeroes :
    ∀ s : ℂ, family s → IsNontrivialZetaZero s →
      ∃ x : Carrier, criticalLinePoint (height x) = s

/-- A local real-spectrum model gives a local height realization. -/
noncomputable def LocalRealSpectrumModel.toLocalHeightRealization
    {family : ℂ → Prop}
    (model : LocalRealSpectrumModel family) :
    LocalHeightRealization family where
  height s hs_family hs_zero :=
    model.height (Classical.choose (model.realizes_family_zeroes s hs_family hs_zero))
  realizes_family_zeroes s hs_family hs_zero :=
    Classical.choose_spec (model.realizes_family_zeroes s hs_family hs_zero)

/-- A local real-spectrum model proves RH on its family. -/
theorem RHOn.of_localRealSpectrumModel {family : ℂ → Prop}
    (model : LocalRealSpectrumModel family) : RHOn family :=
  RHOn.of_localHeightRealization model.toLocalHeightRealization

/-- A finite local real-spectrum model for selected zeroes. -/
structure FiniteLocalRealSpectrumModel (family : ℂ → Prop) extends
    LocalRealSpectrumModel family where
  carrierFintype : Fintype Carrier

attribute [instance] FiniteLocalRealSpectrumModel.carrierFintype

/-- A finite local real-spectrum model proves RH on its family. -/
theorem RHOn.of_finiteLocalRealSpectrumModel {family : ℂ → Prop}
    (model : FiniteLocalRealSpectrumModel family) : RHOn family :=
  RHOn.of_localRealSpectrumModel model.toLocalRealSpectrumModel

end RiemannHypothesisProject
