import RiemannHypothesisProject.SchwartzZeroWindow
import Mathlib.Data.Set.Finite.Basic
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Compact zeta-zero windows

Mathlib proves that the Riemann zeta zero set is discrete, and therefore that
its intersection with any compact subset of `ℂ` is finite. This file turns that
analytic finiteness fact into the finite-window interfaces used by this project.

The result is still local: proving the covered nontrivial zeroes lie on the
critical line remains the mathematical content. The useful checked step is that
compact zeta-zero windows can now be handled by the finite and Schwartz
zero-window machinery.
-/

namespace RiemannHypothesisProject

/-- The finite set of zeta zeroes lying in a compact subset of the complex plane. -/
noncomputable def compactZetaZeroFinset (S : Set ℂ) (hS : IsCompact S) : Finset ℂ :=
  (hS.inter_riemannZetaZeros_finite).toFinset

/-- Membership in the compact zeta-zero finset is exactly membership in the compact window
and being a zeta zero. -/
theorem mem_compactZetaZeroFinset {S : Set ℂ} (hS : IsCompact S) {s : ℂ} :
    s ∈ compactZetaZeroFinset S hS ↔ s ∈ S ∧ IsZetaZero s := by
  rw [compactZetaZeroFinset]
  rw [hS.inter_riemannZetaZeros_finite.mem_toFinset]
  simp [IsZetaZero, riemannZetaZeros]

/-- Every point in the compact zeta-zero finset lies in the compact window. -/
theorem compactZetaZeroFinset_subset_window {S : Set ℂ} (hS : IsCompact S) {s : ℂ}
    (hs : s ∈ compactZetaZeroFinset S hS) : s ∈ S :=
  (mem_compactZetaZeroFinset hS).mp hs |>.1

/-- Every point in the compact zeta-zero finset is a zeta zero. -/
theorem compactZetaZeroFinset_isZetaZero {S : Set ℂ} (hS : IsCompact S) {s : ℂ}
    (hs : s ∈ compactZetaZeroFinset S hS) : IsZetaZero s :=
  (mem_compactZetaZeroFinset hS).mp hs |>.2

/--
A compact zeta-zero window becomes a finite zero-window certificate once the
covered nontrivial zeroes are proved to lie on the critical line.
-/
noncomputable def finiteZeroWindowCertificateOfCompact
    (S : Set ℂ) (hS : IsCompact S)
    (zeroes_on_line :
      ∀ s : ℂ, s ∈ compactZetaZeroFinset S hS →
        IsNontrivialZetaZero s → IsCriticalLine s) :
    FiniteZeroWindowCertificate (fun s : ℂ => s ∈ S) where
  zeroes := compactZetaZeroFinset S hS
  covers_family_zeroes := by
    intro s hs_window hs_zero
    exact (mem_compactZetaZeroFinset hS).mpr ⟨hs_window, hs_zero.1⟩
  zeroes_on_line := zeroes_on_line

/-- A compact zeta-zero window certificate proves local RH on the compact window. -/
theorem RHOn.of_compactZetaZeroWindow
    (S : Set ℂ) (hS : IsCompact S)
    (zeroes_on_line :
      ∀ s : ℂ, s ∈ compactZetaZeroFinset S hS →
        IsNontrivialZetaZero s → IsCriticalLine s) :
    RHOn (fun s : ℂ => s ∈ S) :=
  RHOn.of_finiteZeroWindowCertificate
    (finiteZeroWindowCertificateOfCompact S hS zeroes_on_line)

/-- Schwartz zero-window energy for the actual zeta zeroes in a compact window. -/
noncomputable def schwartzCompactZetaZeroWindowEnergy
    (S : Set ℂ) (hS : IsCompact S) (f : SchwartzLineTestFunction) : ℝ :=
  schwartzZeroWindowEnergy (compactZetaZeroFinset S hS) f

/-- Compact zeta-zero window energy is nonnegative. -/
theorem schwartzCompactZetaZeroWindowEnergy_nonneg
    (S : Set ℂ) (hS : IsCompact S) (f : SchwartzLineTestFunction) :
    0 ≤ schwartzCompactZetaZeroWindowEnergy S hS f := by
  unfold schwartzCompactZetaZeroWindowEnergy
  exact schwartzZeroWindowEnergy_nonneg (compactZetaZeroFinset S hS) f

/-- The compact zeta-zero window weight is summable over all complex numbers. -/
theorem schwartzCompactZetaZeroWindowWeight_summable
    (S : Set ℂ) (hS : IsCompact S) (f : SchwartzLineTestFunction) :
    Summable (schwartzZeroWindowWeight (compactZetaZeroFinset S hS) f) :=
  schwartzZeroWindowWeight_summable (compactZetaZeroFinset S hS) f

/-- The compact zeta-zero window `tsum` is the finite compact-window energy. -/
theorem schwartzCompactZetaZeroWindowWeight_tsum_eq_energy
    (S : Set ℂ) (hS : IsCompact S) (f : SchwartzLineTestFunction) :
    (∑' s : ℂ, schwartzZeroWindowWeight (compactZetaZeroFinset S hS) f s) =
      schwartzCompactZetaZeroWindowEnergy S hS f := by
  unfold schwartzCompactZetaZeroWindowEnergy
  exact schwartzZeroWindowWeight_tsum_eq_energy (compactZetaZeroFinset S hS) f

/--
A compact zeta-zero window with critical-line proofs becomes a Schwartz local
explicit-formula criterion.
-/
noncomputable def schwartzCompactZetaZeroWindowLocalCriterion
    (S : Set ℂ) (hS : IsCompact S)
    (zeroes_on_line :
      ∀ s : ℂ, s ∈ compactZetaZeroFinset S hS →
        IsNontrivialZetaZero s → IsCriticalLine s) :
    SchwartzExplicitFormulaLocalCriterion (fun s : ℂ => s ∈ S) :=
  schwartzZeroWindowLocalCriterion
    (finiteZeroWindowCertificateOfCompact S hS zeroes_on_line)

/-- The Schwartz compact zeta-zero window criterion proves local RH on the compact window. -/
theorem RHOn.of_schwartzCompactZetaZeroWindow
    (S : Set ℂ) (hS : IsCompact S)
    (zeroes_on_line :
      ∀ s : ℂ, s ∈ compactZetaZeroFinset S hS →
        IsNontrivialZetaZero s → IsCriticalLine s) :
    RHOn (fun s : ℂ => s ∈ S) :=
  RHOn.of_schwartzZeroWindowLocalCriterion
    (finiteZeroWindowCertificateOfCompact S hS zeroes_on_line)

end RiemannHypothesisProject
