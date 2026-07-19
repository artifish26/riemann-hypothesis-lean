import RiemannHypothesisProject.SpectralModel
import Mathlib.Data.Finset.Basic

/-!
# Finite zero windows

This file provides a checked certificate shape for finite windows of zeta
zeroes. It is intended for local or numerical experiments: if every nontrivial
zero in a chosen family is covered by a finite set, and every covered point has
a real critical-line height, then RH holds on that family.
-/

namespace RiemannHypothesisProject

/--
A finite set of candidate zeroes that covers all nontrivial zeroes in a chosen
family, together with proofs that covered points lie on the critical line.
-/
structure FiniteZeroWindowCertificate (family : ℂ → Prop) where
  zeroes : Finset ℂ
  covers_family_zeroes :
    ∀ s : ℂ, family s → IsNontrivialZetaZero s → s ∈ zeroes
  zeroes_on_line :
    ∀ s : ℂ, s ∈ zeroes → IsNontrivialZetaZero s → IsCriticalLine s

/-- A finite zero-window certificate proves RH on its family. -/
theorem RHOn.of_finiteZeroWindowCertificate {family : ℂ → Prop}
    (certificate : FiniteZeroWindowCertificate family) : RHOn family := by
  intro s hs_family hs_zero
  exact certificate.zeroes_on_line s
    (certificate.covers_family_zeroes s hs_family hs_zero) hs_zero

/--
A finite zero-window certificate where critical-line membership is supplied by
real heights.
-/
structure FiniteWindowHeightCertificate (family : ℂ → Prop) where
  zeroes : Finset ℂ
  covers_family_zeroes :
    ∀ s : ℂ, family s → IsNontrivialZetaZero s → s ∈ zeroes
  height : ∀ s : ℂ, s ∈ zeroes → ℝ
  realizes_zeroes :
    ∀ (s : ℂ) (hs_zeroes : s ∈ zeroes),
      criticalLinePoint (height s hs_zeroes) = s

/-- A finite height certificate gives a finite zero-window certificate. -/
noncomputable def FiniteWindowHeightCertificate.toFiniteZeroWindowCertificate
    {family : ℂ → Prop}
    (certificate : FiniteWindowHeightCertificate family) :
    FiniteZeroWindowCertificate family where
  zeroes := certificate.zeroes
  covers_family_zeroes := certificate.covers_family_zeroes
  zeroes_on_line s hs_zeroes _ := by
    rw [← certificate.realizes_zeroes s hs_zeroes]
    exact criticalLinePoint_on_line (certificate.height s hs_zeroes)

/-- A finite height certificate proves RH on its family. -/
theorem RHOn.of_finiteWindowHeightCertificate {family : ℂ → Prop}
    (certificate : FiniteWindowHeightCertificate family) : RHOn family :=
  RHOn.of_finiteZeroWindowCertificate
    certificate.toFiniteZeroWindowCertificate

/-- A finite height certificate gives a local real-spectrum model. -/
noncomputable def FiniteWindowHeightCertificate.toLocalRealSpectrumModel
    {family : ℂ → Prop}
    (certificate : FiniteWindowHeightCertificate family) :
    LocalRealSpectrumModel family where
  Carrier := {s : ℂ // s ∈ certificate.zeroes}
  height x := certificate.height x.1 x.2
  realizes_family_zeroes s hs_family hs_zero := by
    let hs_zeroes := certificate.covers_family_zeroes s hs_family hs_zero
    exact ⟨⟨s, hs_zeroes⟩, certificate.realizes_zeroes s hs_zeroes⟩

/-- A finite height certificate gives a finite local real-spectrum model. -/
noncomputable def FiniteWindowHeightCertificate.toFiniteLocalRealSpectrumModel
    {family : ℂ → Prop}
    (certificate : FiniteWindowHeightCertificate family) :
    FiniteLocalRealSpectrumModel family where
  Carrier := {s : ℂ // s ∈ certificate.zeroes}
  height x := certificate.height x.1 x.2
  realizes_family_zeroes s hs_family hs_zero := by
    let hs_zeroes := certificate.covers_family_zeroes s hs_family hs_zero
    exact ⟨⟨s, hs_zeroes⟩, certificate.realizes_zeroes s hs_zeroes⟩
  carrierFintype := Fintype.ofFinset certificate.zeroes (by intro s; simp)

end RiemannHypothesisProject
