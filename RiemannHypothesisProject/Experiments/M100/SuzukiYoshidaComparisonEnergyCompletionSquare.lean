import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaComparisonEnergyTrialSolve

/-!
# B3R-E frozen comparison-energy completion of the square

This module proves the exact finite completion-of-square identity for the
DF6D4 comparison matrices and rational Galerkin trial solves.  The solve
residual remains literal; no invertibility or exact-solve premise is used.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def trialVector {n m : Nat}
    (X : Fin n → Fin m → Real) (x : Fin m → Real) (k : Fin n) : Real :=
  ∑ i : Fin m, X k i * x i

private def crossForm {n m : Nat}
    (C : Fin m → Fin n → Real) (x : Fin m → Real)
    (y : Fin n → Real) : Real :=
  ∑ i : Fin m, x i * ∑ k : Fin n, C i k * y k

private def energyForm {n : Nat}
    (G : Fin n → Fin n → Real) (y z : Fin n → Real) : Real :=
  ∑ k : Fin n, y k * ∑ l : Fin n, G k l * z l

private def baseForm {m : Nat}
    (B : Fin m → Fin m → Real) (x : Fin m → Real) : Real :=
  ∑ i : Fin m, x i * ∑ j : Fin m, B i j * x j

private def residualForm {n m : Nat}
    (R : Fin n → Fin m → Real) (x : Fin m → Real)
    (w : Fin n → Real) : Real :=
  ∑ i : Fin m, x i * ∑ k : Fin n, R k i * w k

private theorem energyForm_symmetric {n : Nat}
    (G : Fin n → Fin n → Real)
    (hG : ∀ k l, G k l = G l k)
    (y z : Fin n → Real) :
    energyForm G y z = energyForm G z y := by
  unfold energyForm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  rw [hG k l]
  ring

private theorem sum_coeff_trial {n m : Nat}
    (X : Fin n → Fin m → Real) (x : Fin m → Real)
    (a : Fin n → Real) :
    (∑ i : Fin m, (∑ k : Fin n, a k * X k i) * x i) =
      ∑ k : Fin n, a k * trialVector X x k := by
  unfold trialVector
  calc
    (∑ i : Fin m, (∑ k : Fin n, a k * X k i) * x i) =
        ∑ i : Fin m, ∑ k : Fin n, (a k * X k i) * x i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = ∑ k : Fin n, ∑ i : Fin m, (a k * X k i) * x i :=
      Finset.sum_comm
    _ = ∑ k : Fin n, a k * ∑ i : Fin m, X k i * x i := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem sum_trial_coeff {n m : Nat}
    (X : Fin n → Fin m → Real) (x : Fin m → Real)
    (a : Fin n → Real) :
    (∑ i : Fin m, (∑ k : Fin n, X k i * a k) * x i) =
      ∑ k : Fin n, trialVector X x k * a k := by
  unfold trialVector
  calc
    (∑ i : Fin m, (∑ k : Fin n, X k i * a k) * x i) =
        ∑ i : Fin m, ∑ k : Fin n, (X k i * a k) * x i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = ∑ k : Fin n, ∑ i : Fin m, (X k i * a k) * x i :=
      Finset.sum_comm
    _ = ∑ k : Fin n, (∑ i : Fin m, X k i * x i) * a k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem residualForm_eq {n m : Nat}
    (C : Fin m → Fin n → Real)
    (G : Fin n → Fin n → Real)
    (X : Fin n → Fin m → Real)
    (R : Fin n → Fin m → Real)
    (hG : ∀ k l, G k l = G l k)
    (hR : ∀ k i, R k i = C i k - ∑ l : Fin n, G k l * X l i)
    (x : Fin m → Real) (w : Fin n → Real) :
    residualForm R x w =
      crossForm C x w - energyForm G (trialVector X x) w := by
  have hmatrix (k : Fin n) :
      (∑ i : Fin m, (∑ l : Fin n, G k l * X l i) * x i) =
        ∑ l : Fin n, G k l * trialVector X x l :=
    sum_coeff_trial X x (G k)
  calc
    residualForm R x w =
        ∑ i : Fin m, x i * ∑ k : Fin n,
          (C i k - ∑ l : Fin n, G k l * X l i) * w k := by
      unfold residualForm
      simp_rw [hR]
    _ = crossForm C x w -
        ∑ i : Fin m, x i * ∑ k : Fin n,
          (∑ l : Fin n, G k l * X l i) * w k := by
      unfold crossForm
      simp_rw [sub_mul, Finset.sum_sub_distrib, mul_sub]
      rw [Finset.sum_sub_distrib]
    _ = crossForm C x w -
        ∑ k : Fin n,
          (∑ i : Fin m, (∑ l : Fin n, G k l * X l i) * x i) * w k := by
      congr 1
      calc
        (∑ i : Fin m, x i * ∑ k : Fin n,
            (∑ l : Fin n, G k l * X l i) * w k) =
            ∑ i : Fin m, ∑ k : Fin n,
              x i * ((∑ l : Fin n, G k l * X l i) * w k) := by
          simp_rw [Finset.mul_sum]
        _ = ∑ k : Fin n, ∑ i : Fin m,
              x i * ((∑ l : Fin n, G k l * X l i) * w k) :=
          Finset.sum_comm
        _ = ∑ k : Fin n, ∑ i : Fin m,
              ((∑ l : Fin n, G k l * X l i) * x i) * w k := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = ∑ k : Fin n,
              (∑ i : Fin m, (∑ l : Fin n, G k l * X l i) * x i) * w k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
    _ = crossForm C x w - energyForm G w (trialVector X x) := by
      unfold energyForm
      simp_rw [hmatrix]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = crossForm C x w - energyForm G (trialVector X x) w := by
      rw [energyForm_symmetric G hG]

private theorem baseForm_eq {n m : Nat}
    (C : Fin m → Fin n → Real)
    (X : Fin n → Fin m → Real)
    (R : Fin n → Fin m → Real)
    (B : Fin m → Fin m → Real)
    (hB : ∀ i j, B i j = ∑ k : Fin n, (C i k * X k j + X k i * R k j))
    (x : Fin m → Real) :
    baseForm B x =
      crossForm C x (trialVector X x) +
        residualForm R x (trialVector X x) := by
  have hcross (i : Fin m) :
      (∑ j : Fin m, (∑ k : Fin n, C i k * X k j) * x j) =
        ∑ k : Fin n, C i k * trialVector X x k :=
    sum_coeff_trial X x (C i)
  have hresidual (j : Fin m) :
      (∑ i : Fin m, (∑ k : Fin n, X k i * R k j) * x i) =
        ∑ k : Fin n, trialVector X x k * R k j :=
    sum_trial_coeff X x (fun k => R k j)
  have hsecond :
      (∑ i : Fin m, x i * ∑ j : Fin m,
        (∑ k : Fin n, X k i * R k j) * x j) =
        ∑ j : Fin m, x j *
          ∑ k : Fin n, R k j * trialVector X x k := by
    calc
      (∑ i : Fin m, x i * ∑ j : Fin m,
          (∑ k : Fin n, X k i * R k j) * x j) =
          ∑ i : Fin m, ∑ j : Fin m,
            x i * ((∑ k : Fin n, X k i * R k j) * x j) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ j : Fin m, ∑ i : Fin m,
            x i * ((∑ k : Fin n, X k i * R k j) * x j) :=
        Finset.sum_comm
      _ = ∑ j : Fin m, x j *
            ∑ i : Fin m, (∑ k : Fin n, X k i * R k j) * x i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ j : Fin m, x j *
            ∑ k : Fin n, R k j * trialVector X x k := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hresidual j]
        apply congrArg
        apply Finset.sum_congr rfl
        intro k _
        ring
  calc
    baseForm B x =
        ∑ i : Fin m, x i * ∑ j : Fin m,
          (∑ k : Fin n, (C i k * X k j + X k i * R k j)) * x j := by
      unfold baseForm
      simp_rw [hB]
    _ =
        (∑ i : Fin m, x i * ∑ j : Fin m,
          (∑ k : Fin n, C i k * X k j) * x j) +
        (∑ i : Fin m, x i * ∑ j : Fin m,
          (∑ k : Fin n, X k i * R k j) * x j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_add_distrib, add_mul]
    _ = crossForm C x (trialVector X x) +
        ∑ j : Fin m, x j *
          ∑ k : Fin n, R k j * trialVector X x k := by
      unfold crossForm
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [hcross i]
    _ = crossForm C x (trialVector X x) +
        residualForm R x (trialVector X x) := by
      rfl

private theorem finite_completion_square {n m : Nat}
    (C : Fin m → Fin n → Real)
    (G : Fin n → Fin n → Real)
    (X : Fin n → Fin m → Real)
    (R : Fin n → Fin m → Real)
    (B : Fin m → Fin m → Real)
    (hG : ∀ k l, G k l = G l k)
    (hR : ∀ k i, R k i = C i k - ∑ l : Fin n, G k l * X l i)
    (hB : ∀ i j, B i j = ∑ k : Fin n, (C i k * X k j + X k i * R k j))
    (x : Fin m → Real) (y : Fin n → Real) :
    2 * crossForm C x y - energyForm G y y =
      baseForm B x +
        2 * residualForm R x (fun k => y k - trialVector X x k) -
        energyForm G (fun k => y k - trialVector X x k)
          (fun k => y k - trialVector X x k) := by
  let z : Fin n → Real := trialVector X x
  have hres (w : Fin n → Real) :
      residualForm R x w = crossForm C x w - energyForm G z w := by
    simpa [z] using residualForm_eq C G X R hG hR x w
  have hbase :
      baseForm B x = 2 * crossForm C x z - energyForm G z z := by
    rw [baseForm_eq C X R B hB x, hres z]
    ring
  have hcross_sub :
      crossForm C x (fun k => y k - z k) =
        crossForm C x y - crossForm C x z := by
    simp [crossForm, mul_sub, Finset.sum_sub_distrib]
  have henergy_sub :
      energyForm G (fun k => y k - z k) (fun k => y k - z k) =
        energyForm G y y - energyForm G y z - energyForm G z y +
          energyForm G z z := by
    simp [energyForm, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have henergy_right_sub :
      energyForm G z (fun k => y k - z k) =
        energyForm G z y - energyForm G z z := by
    simp [energyForm, mul_sub, Finset.sum_sub_distrib]
  have hsymm : energyForm G z y = energyForm G y z :=
    energyForm_symmetric G hG z y
  change 2 * crossForm C x y - energyForm G y y =
    baseForm B x + 2 * residualForm R x (fun k => y k - z k) -
      energyForm G (fun k => y k - z k) (fun k => y k - z k)
  rw [hbase, hres, hcross_sub, henergy_right_sub, henergy_sub, hsymm]
  ring

private theorem evenComparisonGalerkinEntry_symmetric
    (i j : Fin 256) :
    suzukiDF6D4EvenComparisonGalerkinEntry i j =
      suzukiDF6D4EvenComparisonGalerkinEntry j i := by
  by_cases heq : i = j
  · subst j
    rfl
  · by_cases hlt : i.val < j.val
    · have hnot : ¬j.val < i.val := by omega
      have hneji : j ≠ i := Ne.symm heq
      simp [suzukiDF6D4EvenComparisonGalerkinEntry, heq, hneji, hlt, hnot]
    · have hgt : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
        omega
      have hneji : j ≠ i := Ne.symm heq
      simp [suzukiDF6D4EvenComparisonGalerkinEntry, heq, hneji, hlt, hgt]

private theorem oddComparisonGalerkinEntry_symmetric
    (i j : Fin 256) :
    suzukiDF6D4OddComparisonGalerkinEntry i j =
      suzukiDF6D4OddComparisonGalerkinEntry j i := by
  by_cases heq : i = j
  · subst j
    rfl
  · by_cases hlt : i.val < j.val
    · have hnot : ¬j.val < i.val := by omega
      have hneji : j ≠ i := Ne.symm heq
      simp [suzukiDF6D4OddComparisonGalerkinEntry, heq, hneji, hlt, hnot]
    · have hgt : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
        omega
      have hneji : j ≠ i := Ne.symm heq
      simp [suzukiDF6D4OddComparisonGalerkinEntry, heq, hneji, hlt, hgt]

/-- Exact even DF6D4 completion of the square around the rational trial solve. -/
theorem suzukiDF6D5B3RE_evenCompletionSquare
    (x : Fin 45 → Real) (y : Fin 256 → Real) :
    let z : Fin 256 → Real := fun k =>
      ∑ i : Fin 45, (suzukiDF6D4EvenGalerkinApproximant k i : Real) * x i
    2 * (∑ i : Fin 45, x i * ∑ k : Fin 256,
      suzukiDF6D4EvenCompleteCrossEntry i k * y k) -
      (∑ k : Fin 256, y k * ∑ l : Fin 256,
        suzukiDF6D4EvenComparisonGalerkinEntry k l * y l) =
    (∑ i : Fin 45, x i * ∑ j : Fin 45,
      suzukiDF6D4EvenGalerkinBaseEntry i j * x j) +
      2 * (∑ i : Fin 45, x i * ∑ k : Fin 256,
        suzukiDF6D4EvenGalerkinSolveResidual k i * (y k - z k)) -
      (∑ k : Fin 256, (y k - z k) * ∑ l : Fin 256,
        suzukiDF6D4EvenComparisonGalerkinEntry k l * (y l - z l)) := by
  simpa [trialVector, crossForm, energyForm, baseForm, residualForm] using
    finite_completion_square
      suzukiDF6D4EvenCompleteCrossEntry
      suzukiDF6D4EvenComparisonGalerkinEntry
      (fun k i => (suzukiDF6D4EvenGalerkinApproximant k i : Real))
      suzukiDF6D4EvenGalerkinSolveResidual
      suzukiDF6D4EvenGalerkinBaseEntry
      evenComparisonGalerkinEntry_symmetric
      suzukiDF6D5B3RE_evenGalerkinSolveResidual_eq
      (fun i j => by
        unfold suzukiDF6D4EvenGalerkinBaseEntry
        rfl)
      x y

/-- Exact odd DF6D4 completion of the square around the rational trial solve. -/
theorem suzukiDF6D5B3RE_oddCompletionSquare
    (x : Fin 44 → Real) (y : Fin 256 → Real) :
    let z : Fin 256 → Real := fun k =>
      ∑ i : Fin 44, (suzukiDF6D4OddGalerkinApproximant k i : Real) * x i
    2 * (∑ i : Fin 44, x i * ∑ k : Fin 256,
      suzukiDF6D4OddCompleteCrossEntry i k * y k) -
      (∑ k : Fin 256, y k * ∑ l : Fin 256,
        suzukiDF6D4OddComparisonGalerkinEntry k l * y l) =
    (∑ i : Fin 44, x i * ∑ j : Fin 44,
      suzukiDF6D4OddGalerkinBaseEntry i j * x j) +
      2 * (∑ i : Fin 44, x i * ∑ k : Fin 256,
        suzukiDF6D4OddGalerkinSolveResidual k i * (y k - z k)) -
      (∑ k : Fin 256, (y k - z k) * ∑ l : Fin 256,
        suzukiDF6D4OddComparisonGalerkinEntry k l * (y l - z l)) := by
  simpa [trialVector, crossForm, energyForm, baseForm, residualForm] using
    finite_completion_square
      suzukiDF6D4OddCompleteCrossEntry
      suzukiDF6D4OddComparisonGalerkinEntry
      (fun k i => (suzukiDF6D4OddGalerkinApproximant k i : Real))
      suzukiDF6D4OddGalerkinSolveResidual
      suzukiDF6D4OddGalerkinBaseEntry
      oddComparisonGalerkinEntry_symmetric
      suzukiDF6D5B3RE_oddGalerkinSolveResidual_eq
      (fun i j => by
        unfold suzukiDF6D4OddGalerkinBaseEntry
        rfl)
      x y

end

end RiemannHypothesisProject.Experiments.M100
