import RiemannHypothesisProject.StandardExhaustions

/-!
# Closed-ball first-entry shell geometry

The standard zero-counting route uses the closed-ball exhaustion of `Complex`.
This file records the elementary geometry of its first-entry shells.

If a zeta zero first appears in shell `n`, then it lies in the closed ball of
radius `n`; if `0 < n`, it did not lie in the previous closed ball.  These
checked bounds are intended as inputs for later p-series envelope estimates,
where analytic decay in the zero argument must be compared with the shell
index.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

/-- A closed-ball first-entry shell is contained in its closed-ball window. -/
theorem closedBallZero_firstEntryShell_subset_window (n : Nat) :
    closedBallZero.zetaZeroFirstEntryShell n ⊆
      closedBallZero.zetaZeroSubtypeFinset n := by
  intro rho hrho
  exact ((closedBallZero.mem_zetaZeroFirstEntryShell_iff n).mp hrho).1

/-- A zero in the `n`th closed-ball first-entry shell has norm at most `n`. -/
theorem closedBallZero_firstEntryShell_norm_le
    (n : Nat) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroFirstEntryShell n) :
    ‖(rho : Complex)‖ ≤ (n : Real) := by
  have hfinite : rho ∈ closedBallZero.zetaZeroSubtypeFinset n :=
    closedBallZero_firstEntryShell_subset_window n hrho
  have hwindow : (rho : Complex) ∈ closedBallZero.window n :=
    (closedBallZero.mem_zetaZeroSubtypeFinset_iff n).mp hfinite
  have hdist : dist (rho : Complex) 0 ≤ (n : Real) :=
    (mem_closedBallZero_iff n).mp hwindow
  simpa [dist_eq_norm] using hdist

/-- A positive-index first-entry shell member is not in the previous closed-ball window. -/
theorem closedBallZero_firstEntryShell_not_mem_prev_window
    (n : Nat) (hn : 0 < n) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroFirstEntryShell n) :
    (rho : Complex) ∉ closedBallZero.window (n - 1) := by
  have hshell := (closedBallZero.mem_zetaZeroFirstEntryShell_iff n).mp hrho
  have hprev_lt : n - 1 < n := Nat.sub_one_lt (Nat.ne_of_gt hn)
  have hnot_prev :
      rho ∉ closedBallZero.zetaZeroSubtypeFinset (n - 1) :=
    hshell.2 (n - 1) hprev_lt
  intro hwindow
  exact hnot_prev
    ((closedBallZero.mem_zetaZeroSubtypeFinset_iff (n - 1)).mpr hwindow)

/--
A positive-index first-entry shell member has norm strictly larger than the
previous radius.
-/
theorem closedBallZero_firstEntryShell_prev_norm_lt
    (n : Nat) (hn : 0 < n) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroFirstEntryShell n) :
    ((n - 1 : Nat) : Real) < ‖(rho : Complex)‖ := by
  have hnot_window :=
    closedBallZero_firstEntryShell_not_mem_prev_window n hn hrho
  have hnot_dist :
      ¬ dist (rho : Complex) 0 ≤ ((n - 1 : Nat) : Real) := by
    intro hdist
    exact hnot_window ((mem_closedBallZero_iff (n - 1)).mpr hdist)
  have hlt_dist :
      ((n - 1 : Nat) : Real) < dist (rho : Complex) 0 :=
    not_le.mp hnot_dist
  simpa [dist_eq_norm] using hlt_dist

/-- A zero in shell `n + 1` has norm strictly larger than `n`. -/
theorem closedBallZero_firstEntryShell_succ_norm_lt
    (n : Nat) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroFirstEntryShell (n + 1)) :
    (n : Real) < ‖(rho : Complex)‖ := by
  have h :=
    closedBallZero_firstEntryShell_prev_norm_lt (n + 1) (Nat.succ_pos n) hrho
  simpa using h

/-- A zero in shell `n + 1` has norm at most `n + 1`. -/
theorem closedBallZero_firstEntryShell_succ_norm_le
    (n : Nat) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroFirstEntryShell (n + 1)) :
    ‖(rho : Complex)‖ ≤ ((n + 1 : Nat) : Real) :=
  closedBallZero_firstEntryShell_norm_le (n + 1) hrho

/-- The positive-index closed-ball first-entry shell is radially trapped between two radii. -/
theorem closedBallZero_firstEntryShell_norm_between
    (n : Nat) (hn : 0 < n) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroFirstEntryShell n) :
    ((n - 1 : Nat) : Real) < ‖(rho : Complex)‖ ∧
      ‖(rho : Complex)‖ ≤ (n : Real) :=
  ⟨closedBallZero_firstEntryShell_prev_norm_lt n hn hrho,
    closedBallZero_firstEntryShell_norm_le n hrho⟩

/-- The successor-form radial trap avoids predecessor arithmetic in later estimates. -/
theorem closedBallZero_firstEntryShell_succ_norm_between
    (n : Nat) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroFirstEntryShell (n + 1)) :
    (n : Real) < ‖(rho : Complex)‖ ∧
      ‖(rho : Complex)‖ ≤ ((n + 1 : Nat) : Real) :=
  ⟨closedBallZero_firstEntryShell_succ_norm_lt n hrho,
    closedBallZero_firstEntryShell_succ_norm_le n hrho⟩

end ComplexCompactExhaustion

end RiemannHypothesisProject
