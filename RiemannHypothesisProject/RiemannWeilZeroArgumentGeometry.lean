import RiemannHypothesisProject.ClosedBallZeroShellGeometry

/-!
# Geometry of the Riemann-Weil zero argument

The Riemann-Weil zero contribution evaluates a complex extension at

```text
(rho - 1/2) / i.
```

This file records elementary norm comparisons between that shifted argument and
the ordinary complex norm of `rho`.  These lemmas are intended to bridge
source-side analytic decay estimates to the closed-ball first-entry shell
geometry.
-/

namespace RiemannHypothesisProject

/-- Multiplication by `i` recovers the shifted zero coordinate. -/
theorem riemannWeilZeroArgument_mul_I (z : Complex) :
    riemannWeilZeroArgument z * Complex.I = z - (1 / 2 : Complex) := by
  unfold riemannWeilZeroArgument
  field_simp [Complex.I_ne_zero]

/-- Multiplication by `i` preserves the complex norm. -/
theorem norm_mul_I (z : Complex) :
    ‖z * Complex.I‖ = ‖z‖ := by
  rw [norm_mul]
  simp

/-- The Riemann-Weil zero argument has the same norm as `z - 1/2`. -/
theorem norm_riemannWeilZeroArgument_eq_shift (z : Complex) :
    ‖riemannWeilZeroArgument z‖ = ‖z - (1 / 2 : Complex)‖ := by
  have h :=
    congrArg norm (riemannWeilZeroArgument_mul_I z)
  simpa [norm_mul_I] using h

/-- The ordinary zero norm is controlled by the shifted Riemann-Weil argument. -/
theorem norm_le_riemannWeilZeroArgument_norm_add_half_norm (z : Complex) :
    ‖z‖ ≤ ‖riemannWeilZeroArgument z‖ + ‖(1 / 2 : Complex)‖ := by
  have hz : z = (z - (1 / 2 : Complex)) + (1 / 2 : Complex) := by
    ring
  calc
    ‖z‖ = ‖(z - (1 / 2 : Complex)) + (1 / 2 : Complex)‖ := by
      exact congrArg norm hz
    _ ≤ ‖z - (1 / 2 : Complex)‖ + ‖(1 / 2 : Complex)‖ := norm_add_le _ _
    _ = ‖riemannWeilZeroArgument z‖ + ‖(1 / 2 : Complex)‖ := by
      rw [← norm_riemannWeilZeroArgument_eq_shift z]

/--
If `z` is outside a radius `r`, then the Riemann-Weil argument is outside the
radius shifted by `‖1/2‖`.
-/
theorem sub_half_norm_lt_riemannWeilZeroArgument_norm_of_lt_norm
    (z : Complex) {r : Real} (hr : r < ‖z‖) :
    r - ‖(1 / 2 : Complex)‖ < ‖riemannWeilZeroArgument z‖ := by
  have hle := norm_le_riemannWeilZeroArgument_norm_add_half_norm z
  linarith

namespace ComplexCompactExhaustion

/--
The geometric lower bound attached to a closed-ball first-entry shell index.

Shell `0` is assigned the harmless bound `-1`.  Shell `n + 1` uses the radial
lower bound `n`, shifted by the `1 / 2` appearing in the Riemann-Weil zero
argument.
-/
noncomputable def closedBallZeroArgumentShellLowerBound (n : Nat) : Real :=
  match n with
  | 0 => -1
  | k + 1 => (k : Real) - ‖(1 / 2 : Complex)‖

/-- The complex norm of `1 / 2` is at most `1`. -/
theorem norm_half_complex_le_one :
    norm (1 / 2 : Complex) <= (1 : Real) := by
  rw [norm_div, norm_one, Complex.norm_two]
  norm_num

/--
From shell `m + 2` onward, the checked Riemann-Weil zero-argument shell lower
bound dominates the plain tail radius `m`.
-/
theorem nat_le_closedBallZeroArgumentShellLowerBound_add_two (m : Nat) :
    (m : Real) <= closedBallZeroArgumentShellLowerBound (m + 2) := by
  have hhalf : norm (1 / 2 : Complex) <= (1 : Real) :=
    norm_half_complex_le_one
  change (m : Real) <= ((m + 1 : Nat) : Real) - norm (1 / 2 : Complex)
  have hcast : ((m + 1 : Nat) : Real) = (m : Real) + 1 := by
    norm_num
  linarith

/--
In the successor closed-ball shell, the Riemann-Weil zero argument has norm
larger than the previous shell radius shifted by `‖1/2‖`.
-/
theorem closedBallZero_firstEntryShell_succ_sub_half_norm_lt_argument_norm
    (n : Nat) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroFirstEntryShell (n + 1)) :
    (n : Real) - ‖(1 / 2 : Complex)‖ <
      ‖riemannWeilZeroArgument (rho : Complex)‖ := by
  exact
    sub_half_norm_lt_riemannWeilZeroArgument_norm_of_lt_norm
      (rho : Complex)
      (closedBallZero_firstEntryShell_succ_norm_lt n hrho)

/--
Positive-index closed-ball shell members give the same shifted lower bound in
predecessor form.
-/
theorem closedBallZero_firstEntryShell_sub_half_norm_lt_argument_norm
    (n : Nat) (hn : 0 < n) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroFirstEntryShell n) :
    ((n - 1 : Nat) : Real) - ‖(1 / 2 : Complex)‖ <
      ‖riemannWeilZeroArgument (rho : Complex)‖ := by
  exact
    sub_half_norm_lt_riemannWeilZeroArgument_norm_of_lt_norm
      (rho : Complex)
      (closedBallZero_firstEntryShell_prev_norm_lt n hn hrho)

/--
Every zeta zero's first-entry index gives a lower bound for the norm of the
Riemann-Weil zero argument.
-/
theorem closedBallZero_firstEntryIndex_argumentShellLowerBound_lt
    (rho : ZetaZeroSubtype) :
    closedBallZeroArgumentShellLowerBound
        (closedBallZero.zetaZeroFirstEntryIndex rho) <
      ‖riemannWeilZeroArgument (rho : Complex)‖ := by
  set n := closedBallZero.zetaZeroFirstEntryIndex rho with hn
  have hrho :
      rho ∈ closedBallZero.zetaZeroFirstEntryShell n :=
    by simpa [hn] using closedBallZero.mem_zetaZeroFirstEntryIndex rho
  change closedBallZeroArgumentShellLowerBound n <
    ‖riemannWeilZeroArgument (rho : Complex)‖
  cases hcases : n with
  | zero =>
      unfold closedBallZeroArgumentShellLowerBound
      have hnonneg :
          0 <= ‖riemannWeilZeroArgument (rho : Complex)‖ := norm_nonneg _
      linarith
  | succ k =>
      unfold closedBallZeroArgumentShellLowerBound
      have hrho_succ :
          rho ∈ closedBallZero.zetaZeroFirstEntryShell (k + 1) := by
        simpa [hcases] using hrho
      exact
        closedBallZero_firstEntryShell_succ_sub_half_norm_lt_argument_norm
          k hrho_succ

end ComplexCompactExhaustion

end RiemannHypothesisProject
